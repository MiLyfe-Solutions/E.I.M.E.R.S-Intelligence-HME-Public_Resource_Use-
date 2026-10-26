import V185TrunkScan21Chunk166

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2035529 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_2035529 : Nat := 118140960795 + 2035529 * 2 ^ 59
def prefixEnd_2035529 : Nat := 4983230072969 + 3 ^ 40 * 2035529 * 2
def baseEnd_2035529 : Nat := 464535450295942985389457

theorem tailTrace_2035529 : CollatzResearch.WordTrace tailWord_2035529 prefixEnd_2035529 464535450295942985389457 := by
  unfold tailWord_2035529
  simp only [CollatzResearch.WordTrace]
  refine ⟨74241841842633548521221641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49494561228422365680814427 74241841842633548521221641)
  ·
    refine ⟨55681381381975161390916231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74241841842633548521221641 55681381381975161390916231)
    ·
      refine ⟨83522072072962742086374347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55681381381975161390916231 83522072072962742086374347)
      ·
        refine ⟨125283108109444113129561521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83522072072962742086374347 125283108109444113129561521)
        ·
          refine ⟨93962331082083084847171141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125283108109444113129561521 93962331082083084847171141)
          ·
            refine ⟨17617937077890578408844589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93962331082083084847171141 17617937077890578408844589)
            ·
              refine ⟨6606726404208966903316721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17617937077890578408844589 6606726404208966903316721)
              ·
                refine ⟨4955044803156725177487541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606726404208966903316721 4955044803156725177487541)
                ·
                  refine ⟨464535450295942985389457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4955044803156725177487541 464535450295942985389457)
                  ·
                    rfl

theorem cell21_2035529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_2035529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035529 prefixEnd_2035529 := by exact prefixLift 2035529
  have htrace : WordTrace (prefixWord ++ tailWord_2035529) baseStart_2035529 baseEnd_2035529 := by
    simpa [prefixWord, tailWord_2035529, baseEnd_2035529] using wordTrace_append hprefix tailTrace_2035529
  have hstable : (prefixWord ++ tailWord_2035529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035529).length < 2 ^ (prefixWord ++ tailWord_2035529).sum := by decide
  have hdescent : baseEnd_2035529 < baseStart_2035529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035532 : List Nat := [2, 2, 1, 3, 4, 1, 3, 5]
def baseStart_2035532 : Nat := 118140960795 + 2035532 * 2 ^ 59
def prefixEnd_2035532 : Nat := 4983230072969 + 3 ^ 40 * 2035532 * 2
def baseEnd_2035532 : Nat := 154845378312271882279817

theorem tailTrace_2035532 : CollatzResearch.WordTrace tailWord_2035532 prefixEnd_2035532 154845378312271882279817 := by
  unfold tailWord_2035532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37120975630811340016790425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49494634174415120022387233 37120975630811340016790425)
  ·
    refine ⟨27840731723108505012592819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37120975630811340016790425 27840731723108505012592819)
    ·
      refine ⟨41761097584662757518889229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27840731723108505012592819 41761097584662757518889229)
      ·
        refine ⟨15660411594248534069583461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41761097584662757518889229 15660411594248534069583461)
        ·
          refine ⟨2936327173921600138046899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15660411594248534069583461 2936327173921600138046899)
          ·
            refine ⟨4404490760882400207070349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936327173921600138046899 4404490760882400207070349)
            ·
              refine ⟨1651684035330900077651381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4404490760882400207070349 1651684035330900077651381)
              ·
                refine ⟨154845378312271882279817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1651684035330900077651381 154845378312271882279817)
                ·
                  rfl

theorem cell21_2035532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_2035532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035532 prefixEnd_2035532 := by exact prefixLift 2035532
  have htrace : WordTrace (prefixWord ++ tailWord_2035532) baseStart_2035532 baseEnd_2035532 := by
    simpa [prefixWord, tailWord_2035532, baseEnd_2035532] using wordTrace_append hprefix tailTrace_2035532
  have hstable : (prefixWord ++ tailWord_2035532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035532).length < 2 ^ (prefixWord ++ tailWord_2035532).sum := by decide
  have hdescent : baseEnd_2035532 < baseStart_2035532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035560 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_2035560 : Nat := 118140960795 + 2035560 * 2 ^ 59
def prefixEnd_2035560 : Nat := 4983230072969 + 3 ^ 40 * 2035560 * 2
def baseEnd_2035560 : Nat := 464542524918293820372727

theorem tailTrace_2035560 : CollatzResearch.WordTrace tailWord_2035560 prefixEnd_2035560 464542524918293820372727 := by
  unfold tailWord_2035560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37121486252760620407800067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49495315003680827210400089 37121486252760620407800067)
  ·
    refine ⟨55682229379140930611700101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37121486252760620407800067 55682229379140930611700101)
    ·
      refine ⟨10440418008588924489693769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55682229379140930611700101 10440418008588924489693769)
      ·
        refine ⟨7830313506441693367270327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10440418008588924489693769 7830313506441693367270327)
        ·
          refine ⟨11745470259662540050905491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830313506441693367270327 11745470259662540050905491)
          ·
            refine ⟨17618205389493810076358237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11745470259662540050905491 17618205389493810076358237)
            ·
              refine ⟨6606827021060178778634339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17618205389493810076358237 6606827021060178778634339)
              ·
                refine ⟨9910240531590268167951509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606827021060178778634339 9910240531590268167951509)
                ·
                  refine ⟨464542524918293820372727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9910240531590268167951509 464542524918293820372727)
                  ·
                    rfl

theorem cell21_2035560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_2035560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035560 prefixEnd_2035560 := by exact prefixLift 2035560
  have htrace : WordTrace (prefixWord ++ tailWord_2035560) baseStart_2035560 baseEnd_2035560 := by
    simpa [prefixWord, tailWord_2035560, baseEnd_2035560] using wordTrace_append hprefix tailTrace_2035560
  have hstable : (prefixWord ++ tailWord_2035560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035560).length < 2 ^ (prefixWord ++ tailWord_2035560).sum := by decide
  have hdescent : baseEnd_2035560 < baseStart_2035560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035577 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 4]
def baseStart_2035577 : Nat := 118140960795 + 2035577 * 2 ^ 59
def prefixEnd_2035577 : Nat := 4983230072969 + 3 ^ 40 * 2035577 * 2
def baseEnd_2035577 : Nat := 464546404549905568589359

theorem tailTrace_2035577 : CollatzResearch.WordTrace tailWord_2035577 prefixEnd_2035577 464546404549905568589359 := by
  unfold tailWord_2035577
  simp only [CollatzResearch.WordTrace]
  refine ⟨74243592546459652718968985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49495728364306435145979323 74243592546459652718968985)
  ·
    refine ⟨55682694409844739539226739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74243592546459652718968985 55682694409844739539226739)
    ·
      refine ⟨83524041614767109308840109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55682694409844739539226739 83524041614767109308840109)
      ·
        refine ⟨31321515605537665990815041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83524041614767109308840109 31321515605537665990815041)
        ·
          refine ⟨23491136704153249493111281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31321515605537665990815041 23491136704153249493111281)
          ·
            refine ⟨17618352528114937119833461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23491136704153249493111281 17618352528114937119833461)
            ·
              refine ⟨1651720549510775354984387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17618352528114937119833461 1651720549510775354984387)
              ·
                refine ⟨2477580824266163032476581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651720549510775354984387 2477580824266163032476581)
                ·
                  refine ⟨464546404549905568589359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2477580824266163032476581 464546404549905568589359)
                  ·
                    rfl

theorem cell21_2035577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_2035577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035577 prefixEnd_2035577 := by exact prefixLift 2035577
  have htrace : WordTrace (prefixWord ++ tailWord_2035577) baseStart_2035577 baseEnd_2035577 := by
    simpa [prefixWord, tailWord_2035577, baseEnd_2035577] using wordTrace_append hprefix tailTrace_2035577
  have hstable : (prefixWord ++ tailWord_2035577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035577).length < 2 ^ (prefixWord ++ tailWord_2035577).sum := by decide
  have hdescent : baseEnd_2035577 < baseStart_2035577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035591 : List Nat := [1, 1, 4, 2, 4, 1, 1, 7]
def baseStart_2035591 : Nat := 118140960795 + 2035591 * 2 ^ 59
def prefixEnd_2035591 : Nat := 4983230072969 + 3 ^ 40 * 2035591 * 2
def baseEnd_2035591 : Nat := 154849866513548218451999

theorem tailTrace_2035591 : CollatzResearch.WordTrace tailWord_2035591 prefixEnd_2035591 154849866513548218451999 := by
  unfold tailWord_2035591
  simp only [CollatzResearch.WordTrace]
  refine ⟨74244103168408933109978627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49496068778939288739985751 74244103168408933109978627)
  ·
    refine ⟨111366154752613399664967941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74244103168408933109978627 111366154752613399664967941)
    ·
      refine ⟨20881154016115012437181489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111366154752613399664967941 20881154016115012437181489)
      ·
        refine ⟨15660865512086259327886117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20881154016115012437181489 15660865512086259327886117)
        ·
          refine ⟨2936412283516173623978647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15660865512086259327886117 2936412283516173623978647)
          ·
            refine ⟨4404618425274260435967971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936412283516173623978647 4404618425274260435967971)
            ·
              refine ⟨6606927637911390653951957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404618425274260435967971 6606927637911390653951957)
              ·
                refine ⟨154849866513548218451999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6606927637911390653951957 154849866513548218451999)
                ·
                  rfl

theorem cell21_2035591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_2035591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035591 prefixEnd_2035591 := by exact prefixLift 2035591
  have htrace : WordTrace (prefixWord ++ tailWord_2035591) baseStart_2035591 baseEnd_2035591 := by
    simpa [prefixWord, tailWord_2035591, baseEnd_2035591] using wordTrace_append hprefix tailTrace_2035591
  have hstable : (prefixWord ++ tailWord_2035591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035591).length < 2 ^ (prefixWord ++ tailWord_2035591).sum := by decide
  have hdescent : baseEnd_2035591 < baseStart_2035591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035608 : List Nat := [2, 1, 2, 6, 1, 2, 7]
def baseStart_2035608 : Nat := 118140960795 + 2035608 * 2 ^ 59
def prefixEnd_2035608 : Nat := 4983230072969 + 3 ^ 40 * 2035608 * 2
def baseEnd_2035608 : Nat := 51617053241361822619181

theorem tailTrace_2035608 : CollatzResearch.WordTrace tailWord_2035608 prefixEnd_2035608 51617053241361822619181 := by
  unfold tailWord_2035608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37122361604673672506673739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49496482139564896675564985 37122361604673672506673739)
  ·
    refine ⟨55683542407010508760010609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37122361604673672506673739 55683542407010508760010609)
    ·
      refine ⟨41762656805257881570007957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55683542407010508760010609 41762656805257881570007957)
      ·
        refine ⟨1957624537746463198594123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41762656805257881570007957 1957624537746463198594123)
        ·
          refine ⟨2936436806619694797891185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957624537746463198594123 2936436806619694797891185)
          ·
            refine ⟨2202327604964771098418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936436806619694797891185 2202327604964771098418389)
            ·
              refine ⟨51617053241361822619181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2202327604964771098418389 51617053241361822619181)
              ·
                rfl

theorem cell21_2035608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 7].length) (baseStart_2035608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035608 prefixEnd_2035608 := by exact prefixLift 2035608
  have htrace : WordTrace (prefixWord ++ tailWord_2035608) baseStart_2035608 baseEnd_2035608 := by
    simpa [prefixWord, tailWord_2035608, baseEnd_2035608] using wordTrace_append hprefix tailTrace_2035608
  have hstable : (prefixWord ++ tailWord_2035608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035608).length < 2 ^ (prefixWord ++ tailWord_2035608).sum := by decide
  have hdescent : baseEnd_2035608 < baseStart_2035608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035614 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2035614 : Nat := 118140960795 + 2035614 * 2 ^ 59
def prefixEnd_2035614 : Nat := 4983230072969 + 3 ^ 40 * 2035614 * 2
def baseEnd_2035614 : Nat := 464554848454001726472617

theorem tailTrace_2035614 : CollatzResearch.WordTrace tailWord_2035614 prefixEnd_2035614 464554848454001726472617 := by
  unfold tailWord_2035614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280617755915701004758237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49496628031550405358710597 9280617755915701004758237)
  ·
    refine ⟨3480231658468387876784339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9280617755915701004758237 3480231658468387876784339)
    ·
      refine ⟨5220347487702581815176509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480231658468387876784339 5220347487702581815176509)
      ·
        refine ⟨1957630307888468180691191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5220347487702581815176509 1957630307888468180691191)
        ·
          refine ⟨2936445461832702271036787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957630307888468180691191 2936445461832702271036787)
          ·
            refine ⟨4404668192749053406555181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936445461832702271036787 4404668192749053406555181)
            ·
              refine ⟨1651750572280895027458193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4404668192749053406555181 1651750572280895027458193)
              ·
                refine ⟨1238812929210671270593645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651750572280895027458193 1238812929210671270593645)
                ·
                  refine ⟨464554848454001726472617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238812929210671270593645 464554848454001726472617)
                  ·
                    rfl

theorem cell21_2035614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2035614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035614 prefixEnd_2035614 := by exact prefixLift 2035614
  have htrace : WordTrace (prefixWord ++ tailWord_2035614) baseStart_2035614 baseEnd_2035614 := by
    simpa [prefixWord, tailWord_2035614, baseEnd_2035614] using wordTrace_append hprefix tailTrace_2035614
  have hstable : (prefixWord ++ tailWord_2035614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035614).length < 2 ^ (prefixWord ++ tailWord_2035614).sum := by decide
  have hdescent : baseEnd_2035614 < baseStart_2035614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035673 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 3]
def baseStart_2035673 : Nat := 118140960795 + 2035673 * 2 ^ 59
def prefixEnd_2035673 : Nat := 4983230072969 + 3 ^ 40 * 2035673 * 2
def baseEnd_2035673 : Nat := 464568313057830734989163

theorem tailTrace_2035673 : CollatzResearch.WordTrace tailWord_2035673 prefixEnd_2035673 464568313057830734989163 := by
  unfold tailWord_2035673
  simp only [CollatzResearch.WordTrace]
  refine ⟨74247093954111861114463673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49498062636074574076309115 74247093954111861114463673)
  ·
    refine ⟨55685320465583895835847755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74247093954111861114463673 55685320465583895835847755)
    ·
      refine ⟨83527980698375843753771633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55685320465583895835847755 83527980698375843753771633)
      ·
        refine ⟨62645985523781882815328725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83527980698375843753771633 62645985523781882815328725)
        ·
          refine ⟨1468265285713637878484267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62645985523781882815328725 1468265285713637878484267)
          ·
            refine ⟨2202397928570456817726401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468265285713637878484267 2202397928570456817726401)
            ·
              refine ⟨1651798446427842613294801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202397928570456817726401 1651798446427842613294801)
              ·
                refine ⟨1238848834820881959971101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651798446427842613294801 1238848834820881959971101)
                ·
                  refine ⟨464568313057830734989163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238848834820881959971101 464568313057830734989163)
                  ·
                    rfl

theorem cell21_2035673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_2035673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035673 prefixEnd_2035673 := by exact prefixLift 2035673
  have htrace : WordTrace (prefixWord ++ tailWord_2035673) baseStart_2035673 baseEnd_2035673 := by
    simpa [prefixWord, tailWord_2035673, baseEnd_2035673] using wordTrace_append hprefix tailTrace_2035673
  have hstable : (prefixWord ++ tailWord_2035673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035673).length < 2 ^ (prefixWord ++ tailWord_2035673).sum := by decide
  have hdescent : baseEnd_2035673 < baseStart_2035673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035718 : List Nat := [6, 2, 1, 2, 1, 1, 8]
def baseStart_2035718 : Nat := 118140960795 + 2035718 * 2 ^ 59
def prefixEnd_2035718 : Nat := 4983230072969 + 3 ^ 40 * 2035718 * 2
def baseEnd_2035718 : Nat := 51619842518991184082119

theorem tailTrace_2035718 : CollatzResearch.WordTrace tailWord_2035718 prefixEnd_2035718 51619842518991184082119 := by
  unfold tailWord_2035718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320272976217151056245369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49499156825965889199901205 2320272976217151056245369)
  ·
    refine ⟨1740204732162863292184027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320272976217151056245369 1740204732162863292184027)
    ·
      refine ⟨2610307098244294938276041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740204732162863292184027 2610307098244294938276041)
      ·
        refine ⟨1957730323683221203707031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610307098244294938276041 1957730323683221203707031)
        ·
          refine ⟨2936595485524831805560547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957730323683221203707031 2936595485524831805560547)
          ·
            refine ⟨4404893228287247708340821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936595485524831805560547 4404893228287247708340821)
            ·
              refine ⟨51619842518991184082119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4404893228287247708340821 51619842518991184082119)
              ·
                rfl

theorem cell21_2035718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 8].length) (baseStart_2035718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035718 prefixEnd_2035718 := by exact prefixLift 2035718
  have htrace : WordTrace (prefixWord ++ tailWord_2035718) baseStart_2035718 baseEnd_2035718 := by
    simpa [prefixWord, tailWord_2035718, baseEnd_2035718] using wordTrace_append hprefix tailTrace_2035718
  have hstable : (prefixWord ++ tailWord_2035718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035718).length < 2 ^ (prefixWord ++ tailWord_2035718).sum := by decide
  have hdescent : baseEnd_2035718 < baseStart_2035718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035726 : List Nat := [4, 1, 1, 2, 2, 1, 10]
def baseStart_2035726 : Nat := 118140960795 + 2035726 * 2 ^ 59
def prefixEnd_2035726 : Nat := 4983230072969 + 3 ^ 40 * 2035726 * 2
def baseEnd_2035726 : Nat := 51620045375546046733969

theorem tailTrace_2035726 : CollatzResearch.WordTrace tailWord_2035726 prefixEnd_2035726 51620045375546046733969 := by
  unfold tailWord_2035726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281128377864981395767879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49499351348613234110762021 9281128377864981395767879)
  ·
    refine ⟨13921692566797472093651819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9281128377864981395767879 13921692566797472093651819)
    ·
      refine ⟨20882538850196208140477729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921692566797472093651819 20882538850196208140477729)
      ·
        refine ⟨15661904137647156105358297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20882538850196208140477729 15661904137647156105358297)
        ·
          refine ⟨11746428103235367079018723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15661904137647156105358297 11746428103235367079018723)
          ·
            refine ⟨17619642154853050618528085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746428103235367079018723 17619642154853050618528085)
            ·
              refine ⟨51620045375546046733969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17619642154853050618528085 51620045375546046733969)
              ·
                rfl

theorem cell21_2035726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 10].length) (baseStart_2035726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035726 prefixEnd_2035726 := by exact prefixLift 2035726
  have htrace : WordTrace (prefixWord ++ tailWord_2035726) baseStart_2035726 baseEnd_2035726 := by
    simpa [prefixWord, tailWord_2035726, baseEnd_2035726] using wordTrace_append hprefix tailTrace_2035726
  have hstable : (prefixWord ++ tailWord_2035726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035726).length < 2 ^ (prefixWord ++ tailWord_2035726).sum := by decide
  have hdescent : baseEnd_2035726 < baseStart_2035726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035732 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2035732 : Nat := 118140960795 + 2035732 * 2 ^ 59
def prefixEnd_2035732 : Nat := 4983230072969 + 3 ^ 40 * 2035732 * 2
def baseEnd_2035732 : Nat := 464581777661659743505709

theorem tailTrace_2035732 : CollatzResearch.WordTrace tailWord_2035732 prefixEnd_2035732 464581777661659743505709 := by
  unfold tailWord_2035732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124622930449057095430725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49499497240598742793907633 37124622930449057095430725)
  ·
    refine ⟨6960866799459198205393261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37124622930449057095430725 6960866799459198205393261)
    ·
      refine ⟨2610325049797199327022473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6960866799459198205393261 2610325049797199327022473)
      ·
        refine ⟨1957743787347899495266855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610325049797199327022473 1957743787347899495266855)
        ·
          refine ⟨2936615681021849242900283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957743787347899495266855 2936615681021849242900283)
          ·
            refine ⟨4404923521532773864350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936615681021849242900283 4404923521532773864350425)
            ·
              refine ⟨3303692641149580398262819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4404923521532773864350425 3303692641149580398262819)
              ·
                refine ⟨4955538961724370597394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303692641149580398262819 4955538961724370597394229)
                ·
                  refine ⟨464581777661659743505709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4955538961724370597394229 464581777661659743505709)
                  ·
                    rfl

theorem cell21_2035732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2035732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035732 prefixEnd_2035732 := by exact prefixLift 2035732
  have htrace : WordTrace (prefixWord ++ tailWord_2035732) baseStart_2035732 baseEnd_2035732 := by
    simpa [prefixWord, tailWord_2035732, baseEnd_2035732] using wordTrace_append hprefix tailTrace_2035732
  have hstable : (prefixWord ++ tailWord_2035732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035732).length < 2 ^ (prefixWord ++ tailWord_2035732).sum := by decide
  have hdescent : baseEnd_2035732 < baseStart_2035732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035802 : List Nat := [3, 1, 1, 2, 1, 1, 6, 6]
def baseStart_2035802 : Nat := 118140960795 + 2035802 * 2 ^ 59
def prefixEnd_2035802 : Nat := 4983230072969 + 3 ^ 40 * 2035802 * 2
def baseEnd_2035802 : Nat := 154865917538451725779633

theorem tailTrace_2035802 : CollatzResearch.WordTrace tailWord_2035802 prefixEnd_2035802 154865917538451725779633 := by
  unfold tailWord_2035802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18562949742661129036477415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49501199313763010763939773 18562949742661129036477415)
  ·
    refine ⟨27844424613991693554716123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18562949742661129036477415 27844424613991693554716123)
    ·
      refine ⟨41766636920987540332074185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27844424613991693554716123 41766636920987540332074185)
      ·
        refine ⟨31324977690740655249055639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41766636920987540332074185 31324977690740655249055639)
        ·
          refine ⟨46987466536110982873583459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31324977690740655249055639 46987466536110982873583459)
          ·
            refine ⟨70481199804166474310375189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46987466536110982873583459 70481199804166474310375189)
            ·
              refine ⟨3303806240820303483298837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70481199804166474310375189 3303806240820303483298837)
              ·
                refine ⟨154865917538451725779633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3303806240820303483298837 154865917538451725779633)
                ·
                  rfl

theorem cell21_2035802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_2035802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035802 prefixEnd_2035802 := by exact prefixLift 2035802
  have htrace : WordTrace (prefixWord ++ tailWord_2035802) baseStart_2035802 baseEnd_2035802 := by
    simpa [prefixWord, tailWord_2035802, baseEnd_2035802] using wordTrace_append hprefix tailTrace_2035802
  have hstable : (prefixWord ++ tailWord_2035802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035802).length < 2 ^ (prefixWord ++ tailWord_2035802).sum := by decide
  have hdescent : baseEnd_2035802 < baseStart_2035802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035847 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_2035847 : Nat := 118140960795 + 2035847 * 2 ^ 59
def prefixEnd_2035847 : Nat := 4983230072969 + 3 ^ 40 * 2035847 * 2
def baseEnd_2035847 : Nat := 464608022228445099088807

theorem tailTrace_2035847 : CollatzResearch.WordTrace tailWord_2035847 prefixEnd_2035847 464608022228445099088807 := by
  unfold tailWord_2035847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74253440255481488831297795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49502293503654325887531863 74253440255481488831297795)
  ·
    refine ⟨111380160383222233246946693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74253440255481488831297795 111380160383222233246946693)
    ·
      refine ⟨20883780071854168733802505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111380160383222233246946693 20883780071854168733802505)
      ·
        refine ⟨15662835053890626550351879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20883780071854168733802505 15662835053890626550351879)
        ·
          refine ⟨23494252580835939825527819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15662835053890626550351879 23494252580835939825527819)
          ·
            refine ⟨35241378871253909738291729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23494252580835939825527819 35241378871253909738291729)
            ·
              refine ⟨26431034153440432303718797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35241378871253909738291729 26431034153440432303718797)
              ·
                refine ⟨9911637807540162113894549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26431034153440432303718797 9911637807540162113894549)
                ·
                  refine ⟨464608022228445099088807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9911637807540162113894549 464608022228445099088807)
                  ·
                    rfl

theorem cell21_2035847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_2035847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035847 prefixEnd_2035847 := by exact prefixLift 2035847
  have htrace : WordTrace (prefixWord ++ tailWord_2035847) baseStart_2035847 baseEnd_2035847 := by
    simpa [prefixWord, tailWord_2035847, baseEnd_2035847] using wordTrace_append hprefix tailTrace_2035847
  have hstable : (prefixWord ++ tailWord_2035847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035847).length < 2 ^ (prefixWord ++ tailWord_2035847).sum := by decide
  have hdescent : baseEnd_2035847 < baseStart_2035847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035943 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 3]
def baseStart_2035943 : Nat := 118140960795 + 2035943 * 2 ^ 59
def prefixEnd_2035943 : Nat := 4983230072969 + 3 ^ 40 * 2035943 * 2
def baseEnd_2035943 : Nat := 464629930736370265488611

theorem tailTrace_2035943 : CollatzResearch.WordTrace tailWord_2035943 prefixEnd_2035943 464629930736370265488611 := by
  unfold tailWord_2035943
  simp only [CollatzResearch.WordTrace]
  refine ⟨74256941663133697226792483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49504627775422464817861655 74256941663133697226792483)
  ·
    refine ⟨111385412494700545840188725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74256941663133697226792483 111385412494700545840188725)
    ·
      refine ⟨10442382421378176172517693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111385412494700545840188725 10442382421378176172517693)
      ·
        refine ⟨3915893408016816064694135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10442382421378176172517693 3915893408016816064694135)
        ·
          refine ⟨5873840112025224097041203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915893408016816064694135 5873840112025224097041203)
          ·
            refine ⟨8810760168037836145561805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873840112025224097041203 8810760168037836145561805)
            ·
              refine ⟨3304035063014188554585677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8810760168037836145561805 3304035063014188554585677)
              ·
                refine ⟨1239013148630320707969629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3304035063014188554585677 1239013148630320707969629)
                ·
                  refine ⟨464629930736370265488611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239013148630320707969629 464629930736370265488611)
                  ·
                    rfl

theorem cell21_2035943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3].length) (baseStart_2035943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035943 prefixEnd_2035943 := by exact prefixLift 2035943
  have htrace : WordTrace (prefixWord ++ tailWord_2035943) baseStart_2035943 baseEnd_2035943 := by
    simpa [prefixWord, tailWord_2035943, baseEnd_2035943] using wordTrace_append hprefix tailTrace_2035943
  have hstable : (prefixWord ++ tailWord_2035943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035943).length < 2 ^ (prefixWord ++ tailWord_2035943).sum := by decide
  have hdescent : baseEnd_2035943 < baseStart_2035943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035954 : List Nat := [3, 2, 1, 3, 2, 1, 9]
def baseStart_2035954 : Nat := 118140960795 + 2035954 * 2 ^ 59
def prefixEnd_2035954 : Nat := 4983230072969 + 3 ^ 40 * 2035954 * 2
def baseEnd_2035954 : Nat := 51625826787359632311695

theorem tailTrace_2035954 : CollatzResearch.WordTrace tailWord_2035954 prefixEnd_2035954 51625826787359632311695 := by
  unfold tailWord_2035954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564335716523461526360729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49504895244062564070295277 18564335716523461526360729)
  ·
    refine ⟨13923251787392596144770547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18564335716523461526360729 13923251787392596144770547)
    ·
      refine ⟨20884877681088894217155821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923251787392596144770547 20884877681088894217155821)
      ·
        refine ⟨7831829130408335331433433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20884877681088894217155821 7831829130408335331433433)
        ·
          refine ⟨5873871847806251498575075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7831829130408335331433433 5873871847806251498575075)
          ·
            refine ⟨8810807771709377247862613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873871847806251498575075 8810807771709377247862613)
            ·
              refine ⟨51625826787359632311695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8810807771709377247862613 51625826787359632311695)
              ·
                rfl

theorem cell21_2035954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 9].length) (baseStart_2035954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2035954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2035954 prefixEnd_2035954 := by exact prefixLift 2035954
  have htrace : WordTrace (prefixWord ++ tailWord_2035954) baseStart_2035954 baseEnd_2035954 := by
    simpa [prefixWord, tailWord_2035954, baseEnd_2035954] using wordTrace_append hprefix tailTrace_2035954
  have hstable : (prefixWord ++ tailWord_2035954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035954).length < 2 ^ (prefixWord ++ tailWord_2035954).sum := by decide
  have hdescent : baseEnd_2035954 < baseStart_2035954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036089 : List Nat := [1, 2, 1, 3, 2, 1, 1, 10]
def baseStart_2036089 : Nat := 118140960795 + 2036089 * 2 ^ 59
def prefixEnd_2036089 : Nat := 4983230072969 + 3 ^ 40 * 2036089 * 2
def baseEnd_2036089 : Nat := 154887749975168818684993

theorem tailTrace_2036089 : CollatzResearch.WordTrace tailWord_2036089 prefixEnd_2036089 154887749975168818684993 := by
  unfold tailWord_2036089
  simp only [CollatzResearch.WordTrace]
  refine ⟨74262266720604764161607321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49508177813736509441071547 74262266720604764161607321)
  ·
    refine ⟨55696700040453573121205491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74262266720604764161607321 55696700040453573121205491)
    ·
      refine ⟨83545050060680359681808237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55696700040453573121205491 83545050060680359681808237)
      ·
        refine ⟨31329393772755134880678089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83545050060680359681808237 31329393772755134880678089)
        ·
          refine ⟨23497045329566351160508567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31329393772755134880678089 23497045329566351160508567)
          ·
            refine ⟨35245567994349526740762851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23497045329566351160508567 35245567994349526740762851)
            ·
              refine ⟨52868351991524290111144277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35245567994349526740762851 52868351991524290111144277)
              ·
                refine ⟨154887749975168818684993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52868351991524290111144277 154887749975168818684993)
                ·
                  rfl

theorem cell21_2036089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_2036089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036089 prefixEnd_2036089 := by exact prefixLift 2036089
  have htrace : WordTrace (prefixWord ++ tailWord_2036089) baseStart_2036089 baseEnd_2036089 := by
    simpa [prefixWord, tailWord_2036089, baseEnd_2036089] using wordTrace_append hprefix tailTrace_2036089
  have hstable : (prefixWord ++ tailWord_2036089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036089).length < 2 ^ (prefixWord ++ tailWord_2036089).sum := by decide
  have hdescent : baseEnd_2036089 < baseStart_2036089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036098 : List Nat := [3, 4, 2, 1, 3, 1, 2, 5]
def baseStart_2036098 : Nat := 118140960795 + 2036098 * 2 ^ 59
def prefixEnd_2036098 : Nat := 4983230072969 + 3 ^ 40 * 2036098 * 2
def baseEnd_2036098 : Nat := 154888434616041480134987

theorem tailTrace_2036098 : CollatzResearch.WordTrace tailWord_2036098 prefixEnd_2036098 154888434616041480134987 := by
  unfold tailWord_2036098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18565648744393039674671237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49508396651714772465789965 18565648744393039674671237)
  ·
    refine ⟨3481059139573694939000857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18565648744393039674671237 3481059139573694939000857)
    ·
      refine ⟨2610794354680271204250643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3481059139573694939000857 2610794354680271204250643)
      ·
        refine ⟨3916191532020406806375965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610794354680271204250643 3916191532020406806375965)
        ·
          refine ⟨1468571824507652552390987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3916191532020406806375965 1468571824507652552390987)
          ·
            refine ⟨2202857736761478828586481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468571824507652552390987 2202857736761478828586481)
            ·
              refine ⟨1652143302571109121439861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202857736761478828586481 1652143302571109121439861)
              ·
                refine ⟨154888434616041480134987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652143302571109121439861 154888434616041480134987)
                ·
                  rfl

theorem cell21_2036098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_2036098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036098 prefixEnd_2036098 := by exact prefixLift 2036098
  have htrace : WordTrace (prefixWord ++ tailWord_2036098) baseStart_2036098 baseEnd_2036098 := by
    simpa [prefixWord, tailWord_2036098, baseEnd_2036098] using wordTrace_append hprefix tailTrace_2036098
  have hstable : (prefixWord ++ tailWord_2036098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036098).length < 2 ^ (prefixWord ++ tailWord_2036098).sum := by decide
  have hdescent : baseEnd_2036098 < baseStart_2036098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036137 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 3]
def baseStart_2036137 : Nat := 118140960795 + 2036137 * 2 ^ 59
def prefixEnd_2036137 : Nat := 4983230072969 + 3 ^ 40 * 2036137 * 2
def baseEnd_2036137 : Nat := 464674204179469039254881

theorem tailTrace_2036137 : CollatzResearch.WordTrace tailWord_2036137 prefixEnd_2036137 464674204179469039254881 := by
  unfold tailWord_2036137
  simp only [CollatzResearch.WordTrace]
  refine ⟨74264017424430868359354665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49509344949620578906236443 74264017424430868359354665)
  ·
    refine ⟨55698013068323151269515999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74264017424430868359354665 55698013068323151269515999)
    ·
      refine ⟨83547019602484726904273999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55698013068323151269515999 83547019602484726904273999)
      ·
        refine ⟨125320529403727090356410999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83547019602484726904273999 125320529403727090356410999)
        ·
          refine ⟨187980794105590635534616499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125320529403727090356410999 187980794105590635534616499)
          ·
            refine ⟨281971191158385953301924749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187980794105590635534616499 281971191158385953301924749)
            ·
              refine ⟨105739196684394732488221781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281971191158385953301924749 105739196684394732488221781)
              ·
                refine ⟨1239131211145250771346349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 105739196684394732488221781 1239131211145250771346349)
                ·
                  refine ⟨464674204179469039254881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239131211145250771346349 464674204179469039254881)
                  ·
                    rfl

theorem cell21_2036137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_2036137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036137 prefixEnd_2036137 := by exact prefixLift 2036137
  have htrace : WordTrace (prefixWord ++ tailWord_2036137) baseStart_2036137 baseEnd_2036137 := by
    simpa [prefixWord, tailWord_2036137, baseEnd_2036137] using wordTrace_append hprefix tailTrace_2036137
  have hstable : (prefixWord ++ tailWord_2036137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036137).length < 2 ^ (prefixWord ++ tailWord_2036137).sum := by decide
  have hdescent : baseEnd_2036137 < baseStart_2036137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036272 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_2036272 : Nat := 118140960795 + 2036272 * 2 ^ 59
def prefixEnd_2036272 : Nat := 4983230072969 + 3 ^ 40 * 2036272 * 2
def baseEnd_2036272 : Nat := 464705013018738804504605

theorem tailTrace_2036272 : CollatzResearch.WordTrace tailWord_2036272 prefixEnd_2036272 464705013018738804504605 := by
  unfold tailWord_2036272
  simp only [CollatzResearch.WordTrace]
  refine ⟨37134470639470893207759535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49512627519294524277012713 37134470639470893207759535)
  ·
    refine ⟨55701705959206339811639303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37134470639470893207759535 55701705959206339811639303)
    ·
      refine ⟨83552558938809509717458955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55701705959206339811639303 83552558938809509717458955)
      ·
        refine ⟨125328838408214264576188433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83552558938809509717458955 125328838408214264576188433)
        ·
          refine ⟨93996628806160698432141325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125328838408214264576188433 93996628806160698432141325)
          ·
            refine ⟨35248735802310261912052997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93996628806160698432141325 35248735802310261912052997)
            ·
              refine ⟨6609137962933174108509937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35248735802310261912052997 6609137962933174108509937)
              ·
                refine ⟨4956853472199880581382453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609137962933174108509937 4956853472199880581382453)
                ·
                  refine ⟨464705013018738804504605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4956853472199880581382453 464705013018738804504605)
                  ·
                    rfl

theorem cell21_2036272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_2036272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036272 prefixEnd_2036272 := by exact prefixLift 2036272
  have htrace : WordTrace (prefixWord ++ tailWord_2036272) baseStart_2036272 baseEnd_2036272 := by
    simpa [prefixWord, tailWord_2036272, baseEnd_2036272] using wordTrace_append hprefix tailTrace_2036272
  have hstable : (prefixWord ++ tailWord_2036272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036272).length < 2 ^ (prefixWord ++ tailWord_2036272).sum := by decide
  have hdescent : baseEnd_2036272 < baseStart_2036272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036320 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_2036320 : Nat := 118140960795 + 2036320 * 2 ^ 59
def prefixEnd_2036320 : Nat := 4983230072969 + 3 ^ 40 * 2036320 * 2
def baseEnd_2036320 : Nat := 464715967272701387704507

theorem tailTrace_2036320 : CollatzResearch.WordTrace tailWord_2036320 prefixEnd_2036320 464715967272701387704507 := by
  unfold tailWord_2036320
  simp only [CollatzResearch.WordTrace]
  refine ⟨37135345991383945306633207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49513794655178593742177609 37135345991383945306633207)
  ·
    refine ⟨55703018987075917959949811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37135345991383945306633207 55703018987075917959949811)
    ·
      refine ⟨83554528480613876939924717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55703018987075917959949811 83554528480613876939924717)
      ·
        refine ⟨31332948180230203852471769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83554528480613876939924717 31332948180230203852471769)
        ·
          refine ⟨23499711135172652889353827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31332948180230203852471769 23499711135172652889353827)
          ·
            refine ⟨35249566702758979334030741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23499711135172652889353827 35249566702758979334030741)
            ·
              refine ⟨1652323439191827156282691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35249566702758979334030741 1652323439191827156282691)
              ·
                refine ⟨2478485158787740734424037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652323439191827156282691 2478485158787740734424037)
                ·
                  refine ⟨464715967272701387704507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2478485158787740734424037 464715967272701387704507)
                  ·
                    rfl

theorem cell21_2036320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_2036320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036320 prefixEnd_2036320 := by exact prefixLift 2036320
  have htrace : WordTrace (prefixWord ++ tailWord_2036320) baseStart_2036320 baseEnd_2036320 := by
    simpa [prefixWord, tailWord_2036320, baseEnd_2036320] using wordTrace_append hprefix tailTrace_2036320
  have hstable : (prefixWord ++ tailWord_2036320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036320).length < 2 ^ (prefixWord ++ tailWord_2036320).sum := by decide
  have hdescent : baseEnd_2036320 < baseStart_2036320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036334 : List Nat := [4, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2036334 : Nat := 118140960795 + 2036334 * 2 ^ 59
def prefixEnd_2036334 : Nat := 4983230072969 + 3 ^ 40 * 2036334 * 2
def baseEnd_2036334 : Nat := 154906387421146824823715

theorem tailTrace_2036334 : CollatzResearch.WordTrace tailWord_2036334 prefixEnd_2036334 154906387421146824823715 := by
  unfold tailWord_2036334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283900325589646375534507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49514135069811447336184037 9283900325589646375534507)
  ·
    refine ⟨13925850488384469563301761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9283900325589646375534507 13925850488384469563301761)
    ·
      refine ⟨10444387866288352172476321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13925850488384469563301761 10444387866288352172476321)
      ·
        refine ⟨7833290899716264129357241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10444387866288352172476321 7833290899716264129357241)
        ·
          refine ⟨5874968174787198097017931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7833290899716264129357241 5874968174787198097017931)
          ·
            refine ⟨8812452262180797145526897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874968174787198097017931 8812452262180797145526897)
            ·
              refine ⟨6609339196635597859145173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812452262180797145526897 6609339196635597859145173)
              ·
                refine ⟨154906387421146824823715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6609339196635597859145173 154906387421146824823715)
                ·
                  rfl

theorem cell21_2036334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2036334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036334 prefixEnd_2036334 := by exact prefixLift 2036334
  have htrace : WordTrace (prefixWord ++ tailWord_2036334) baseStart_2036334 baseEnd_2036334 := by
    simpa [prefixWord, tailWord_2036334, baseEnd_2036334] using wordTrace_append hprefix tailTrace_2036334
  have hstable : (prefixWord ++ tailWord_2036334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036334).length < 2 ^ (prefixWord ++ tailWord_2036334).sum := by decide
  have hdescent : baseEnd_2036334 < baseStart_2036334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036424 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_2036424 : Nat := 118140960795 + 2036424 * 2 ^ 59
def prefixEnd_2036424 : Nat := 4983230072969 + 3 ^ 40 * 2036424 * 2
def baseEnd_2036424 : Nat := 464739701489620317970961

theorem tailTrace_2036424 : CollatzResearch.WordTrace tailWord_2036424 prefixEnd_2036424 464739701489620317970961 := by
  unfold tailWord_2036424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137242587195558187526163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49516323449594077583368217 37137242587195558187526163)
  ·
    refine ⟨55705863880793337281289245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37137242587195558187526163 55705863880793337281289245)
    ·
      refine ⟨20889698955297501480483467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55705863880793337281289245 20889698955297501480483467)
      ·
        refine ⟨31334548432946252220725201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20889698955297501480483467 31334548432946252220725201)
        ·
          refine ⟨23500911324709689165543901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31334548432946252220725201 23500911324709689165543901)
          ·
            refine ⟨8812841746766133437078963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23500911324709689165543901 8812841746766133437078963)
            ·
              refine ⟨13219262620149200155618445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812841746766133437078963 13219262620149200155618445)
              ·
                refine ⟨4957223482555950058356917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13219262620149200155618445 4957223482555950058356917)
                ·
                  refine ⟨464739701489620317970961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4957223482555950058356917 464739701489620317970961)
                  ·
                    rfl

theorem cell21_2036424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_2036424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036424 prefixEnd_2036424 := by exact prefixLift 2036424
  have htrace : WordTrace (prefixWord ++ tailWord_2036424) baseStart_2036424 baseEnd_2036424 := by
    simpa [prefixWord, tailWord_2036424, baseEnd_2036424] using wordTrace_append hprefix tailTrace_2036424
  have hstable : (prefixWord ++ tailWord_2036424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036424).length < 2 ^ (prefixWord ++ tailWord_2036424).sum := by decide
  have hdescent : baseEnd_2036424 < baseStart_2036424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036444 : List Nat := [2, 2, 5, 1, 1, 3, 2, 5]
def baseStart_2036444 : Nat := 118140960795 + 2036444 * 2 ^ 59
def prefixEnd_2036444 : Nat := 4983230072969 + 3 ^ 40 * 2036444 * 2
def baseEnd_2036444 : Nat := 154914755254034909212529

theorem tailTrace_2036444 : CollatzResearch.WordTrace tailWord_2036444 prefixEnd_2036444 154914755254034909212529 := by
  unfold tailWord_2036444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137607317159329895390193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49516809756212439860520257 37137607317159329895390193)
  ·
    refine ⟨27853205487869497421542645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37137607317159329895390193 27853205487869497421542645)
    ·
      refine ⟨2611238014487765383269623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27853205487869497421542645 2611238014487765383269623)
      ·
        refine ⟨3916857021731648074904435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611238014487765383269623 3916857021731648074904435)
        ·
          refine ⟨5875285532597472112356653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916857021731648074904435 5875285532597472112356653)
          ·
            refine ⟨2203232074724052042133745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5875285532597472112356653 2203232074724052042133745)
            ·
              refine ⟨1652424056043039031600309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203232074724052042133745 1652424056043039031600309)
              ·
                refine ⟨154914755254034909212529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652424056043039031600309 154914755254034909212529)
                ·
                  rfl

theorem cell21_2036444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_2036444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036444 prefixEnd_2036444 := by exact prefixLift 2036444
  have htrace : WordTrace (prefixWord ++ tailWord_2036444) baseStart_2036444 baseEnd_2036444 := by
    simpa [prefixWord, tailWord_2036444, baseEnd_2036444] using wordTrace_append hprefix tailTrace_2036444
  have hstable : (prefixWord ++ tailWord_2036444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036444).length < 2 ^ (prefixWord ++ tailWord_2036444).sum := by decide
  have hdescent : baseEnd_2036444 < baseStart_2036444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036517 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2036517 : Nat := 118140960795 + 2036517 * 2 ^ 59
def prefixEnd_2036517 : Nat := 4983230072969 + 3 ^ 40 * 2036517 * 2
def baseEnd_2036517 : Nat := 464760925356672822920771

theorem tailTrace_2036517 : CollatzResearch.WordTrace tailWord_2036517 prefixEnd_2036517 464760925356672822920771 := by
  unfold tailWord_2036517
  simp only [CollatzResearch.WordTrace]
  refine ⟨74277877163054193258187805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49518584775369462172125203 74277877163054193258187805)
  ·
    refine ⟨27854203936145322471820427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74277877163054193258187805 27854203936145322471820427)
    ·
      refine ⟨41781305904217983707730641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27854203936145322471820427 41781305904217983707730641)
      ·
        refine ⟨31335979428163487780797981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41781305904217983707730641 31335979428163487780797981)
        ·
          refine ⟨11750992285561307917799243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31335979428163487780797981 11750992285561307917799243)
          ·
            refine ⟨17626488428341961876698865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11750992285561307917799243 17626488428341961876698865)
            ·
              refine ⟨13219866321256471407524149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626488428341961876698865 13219866321256471407524149)
              ·
                refine ⟨1239362467617794194455389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13219866321256471407524149 1239362467617794194455389)
                ·
                  refine ⟨464760925356672822920771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239362467617794194455389 464760925356672822920771)
                  ·
                    rfl

theorem cell21_2036517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2036517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036517 prefixEnd_2036517 := by exact prefixLift 2036517
  have htrace : WordTrace (prefixWord ++ tailWord_2036517) baseStart_2036517 baseEnd_2036517 := by
    simpa [prefixWord, tailWord_2036517, baseEnd_2036517] using wordTrace_append hprefix tailTrace_2036517
  have hstable : (prefixWord ++ tailWord_2036517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036517).length < 2 ^ (prefixWord ++ tailWord_2036517).sum := by decide
  have hdescent : baseEnd_2036517 < baseStart_2036517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036531 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_2036531 : Nat := 118140960795 + 2036531 * 2 ^ 59
def prefixEnd_2036531 : Nat := 4983230072969 + 3 ^ 40 * 2036531 * 2
def baseEnd_2036531 : Nat := 464764120347411909687409

theorem tailTrace_2036531 : CollatzResearch.WordTrace tailWord_2036531 prefixEnd_2036531 464764120347411909687409 := by
  unfold tailWord_2036531
  simp only [CollatzResearch.WordTrace]
  refine ⟨74278387785003473649197447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49518925190002315766131631 74278387785003473649197447)
  ·
    refine ⟨111417581677505210473796171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74278387785003473649197447 111417581677505210473796171)
    ·
      refine ⟨167126372516257815710694257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111417581677505210473796171 167126372516257815710694257)
      ·
        refine ⟨125344779387193361783020693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167126372516257815710694257 125344779387193361783020693)
        ·
          refine ⟨5875536533774688833579095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125344779387193361783020693 5875536533774688833579095)
          ·
            refine ⟨8813304800662033250368643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875536533774688833579095 8813304800662033250368643)
            ·
              refine ⟨13219957200993049875552965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813304800662033250368643 13219957200993049875552965)
              ·
                refine ⟨2478741975186196851666181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13219957200993049875552965 2478741975186196851666181)
                ·
                  refine ⟨464764120347411909687409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2478741975186196851666181 464764120347411909687409)
                  ·
                    rfl

theorem cell21_2036531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_2036531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036531 prefixEnd_2036531 := by exact prefixLift 2036531
  have htrace : WordTrace (prefixWord ++ tailWord_2036531) baseStart_2036531 baseEnd_2036531 := by
    simpa [prefixWord, tailWord_2036531, baseEnd_2036531] using wordTrace_append hprefix tailTrace_2036531
  have hstable : (prefixWord ++ tailWord_2036531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036531).length < 2 ^ (prefixWord ++ tailWord_2036531).sum := by decide
  have hdescent : baseEnd_2036531 < baseStart_2036531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036562 : List Nat := [3, 2, 2, 1, 1, 2, 5, 5]
def baseStart_2036562 : Nat := 118140960795 + 2036562 * 2 ^ 59
def prefixEnd_2036562 : Nat := 4983230072969 + 3 ^ 40 * 2036562 * 2
def baseEnd_2036562 : Nat := 154923731656587581556893

theorem tailTrace_2036562 : CollatzResearch.WordTrace tailWord_2036562 prefixEnd_2036562 154923731656587581556893 := by
  unfold tailWord_2036562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18569879611972791485893985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49519678965260777295717293 18569879611972791485893985)
  ·
    refine ⟨13927409708979593614420489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18569879611972791485893985 13927409708979593614420489)
    ·
      refine ⟨10445557281734695210815367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13927409708979593614420489 10445557281734695210815367)
      ·
        refine ⟨15668335922602042816223051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10445557281734695210815367 15668335922602042816223051)
        ·
          refine ⟨23502503883903064224334577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15668335922602042816223051 23502503883903064224334577)
          ·
            refine ⟨17626877912927298168250933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23502503883903064224334577 17626877912927298168250933)
            ·
              refine ⟨1652519804336934203273525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17626877912927298168250933 1652519804336934203273525)
              ·
                refine ⟨154923731656587581556893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652519804336934203273525 154923731656587581556893)
                ·
                  rfl

theorem cell21_2036562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_2036562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036562 prefixEnd_2036562 := by exact prefixLift 2036562
  have htrace : WordTrace (prefixWord ++ tailWord_2036562) baseStart_2036562 baseEnd_2036562 := by
    simpa [prefixWord, tailWord_2036562, baseEnd_2036562] using wordTrace_append hprefix tailTrace_2036562
  have hstable : (prefixWord ++ tailWord_2036562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036562).length < 2 ^ (prefixWord ++ tailWord_2036562).sum := by decide
  have hdescent : baseEnd_2036562 < baseStart_2036562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036593 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 3]
def baseStart_2036593 : Nat := 118140960795 + 2036593 * 2 ^ 59
def prefixEnd_2036593 : Nat := 4983230072969 + 3 ^ 40 * 2036593 * 2
def baseEnd_2036593 : Nat := 464778269592113579653949

theorem tailTrace_2036593 : CollatzResearch.WordTrace tailWord_2036593 prefixEnd_2036593 464778269592113579653949 := by
  unfold tailWord_2036593
  simp only [CollatzResearch.WordTrace]
  refine ⟨74280649110778858237954433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49520432740519238825302955 74280649110778858237954433)
  ·
    refine ⟨55710486833084143678465825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74280649110778858237954433 55710486833084143678465825)
    ·
      refine ⟨41782865124813107758849369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55710486833084143678465825 41782865124813107758849369)
      ·
        refine ⟨31337148843609830819137027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41782865124813107758849369 31337148843609830819137027)
        ·
          refine ⟨47005723265414746228705541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31337148843609830819137027 47005723265414746228705541)
          ·
            refine ⟨8813573112265264917882289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47005723265414746228705541 8813573112265264917882289)
            ·
              refine ⟨6610179834198948688411717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8813573112265264917882289 6610179834198948688411717)
              ·
                refine ⟨1239408718912302879077197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6610179834198948688411717 1239408718912302879077197)
                ·
                  refine ⟨464778269592113579653949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239408718912302879077197 464778269592113579653949)
                  ·
                    rfl

theorem cell21_2036593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_2036593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036593 prefixEnd_2036593 := by exact prefixLift 2036593
  have htrace : WordTrace (prefixWord ++ tailWord_2036593) baseStart_2036593 baseEnd_2036593 := by
    simpa [prefixWord, tailWord_2036593, baseEnd_2036593] using wordTrace_append hprefix tailTrace_2036593
  have hstable : (prefixWord ++ tailWord_2036593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036593).length < 2 ^ (prefixWord ++ tailWord_2036593).sum := by decide
  have hdescent : baseEnd_2036593 < baseStart_2036593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036703 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 3]
def baseStart_2036703 : Nat := 118140960795 + 2036703 * 2 ^ 59
def prefixEnd_2036703 : Nat := 4983230072969 + 3 ^ 40 * 2036703 * 2
def baseEnd_2036703 : Nat := 464803373090777832820391

theorem tailTrace_2036703 : CollatzResearch.WordTrace tailWord_2036703 prefixEnd_2036703 464803373090777832820391 := by
  unfold tailWord_2036703
  simp only [CollatzResearch.WordTrace]
  refine ⟨74284661140380347024458763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49523107426920231349639175 74284661140380347024458763)
  ·
    refine ⟨111426991710570520536688145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74284661140380347024458763 111426991710570520536688145)
    ·
      refine ⟨83570243782927890402516109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111426991710570520536688145 83570243782927890402516109)
      ·
        refine ⟨31338841418597958900943541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83570243782927890402516109 31338841418597958900943541)
        ·
          refine ⟨2938016382993558646963457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31338841418597958900943541 2938016382993558646963457)
          ·
            refine ⟨2203512287245168985222593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938016382993558646963457 2203512287245168985222593)
            ·
              refine ⟨1652634215433876738916945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203512287245168985222593 1652634215433876738916945)
              ·
                refine ⟨1239475661575407554187709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652634215433876738916945 1239475661575407554187709)
                ·
                  refine ⟨464803373090777832820391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239475661575407554187709 464803373090777832820391)
                  ·
                    rfl

theorem cell21_2036703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3].length) (baseStart_2036703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036703 prefixEnd_2036703 := by exact prefixLift 2036703
  have htrace : WordTrace (prefixWord ++ tailWord_2036703) baseStart_2036703 baseEnd_2036703 := by
    simpa [prefixWord, tailWord_2036703, baseEnd_2036703] using wordTrace_append hprefix tailTrace_2036703
  have hstable : (prefixWord ++ tailWord_2036703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036703).length < 2 ^ (prefixWord ++ tailWord_2036703).sum := by decide
  have hdescent : baseEnd_2036703 < baseStart_2036703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036714 : List Nat := [3, 1, 3, 1, 2, 4, 1, 6]
def baseStart_2036714 : Nat := 118140960795 + 2036714 * 2 ^ 59
def prefixEnd_2036714 : Nat := 4983230072969 + 3 ^ 40 * 2036714 * 2
def baseEnd_2036714 : Nat := 154935294480214752712345

theorem tailTrace_2036714 : CollatzResearch.WordTrace tailWord_2036714 prefixEnd_2036714 154935294480214752712345 := by
  unfold tailWord_2036714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571265585835123975777299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49523374895560330602072797 18571265585835123975777299)
  ·
    refine ⟨27856898378752685963665949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18571265585835123975777299 27856898378752685963665949)
    ·
      refine ⟨10446336892032257236374731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27856898378752685963665949 10446336892032257236374731)
      ·
        refine ⟨15669505338048385854562097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446336892032257236374731 15669505338048385854562097)
        ·
          refine ⟨11752129003536289390921573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669505338048385854562097 11752129003536289390921573)
          ·
            refine ⟨2203524188163054260797795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11752129003536289390921573 2203524188163054260797795)
            ·
              refine ⟨3305286282244581391196693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203524188163054260797795 3305286282244581391196693)
              ·
                refine ⟨154935294480214752712345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3305286282244581391196693 154935294480214752712345)
                ·
                  rfl

theorem cell21_2036714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_2036714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036714 prefixEnd_2036714 := by exact prefixLift 2036714
  have htrace : WordTrace (prefixWord ++ tailWord_2036714) baseStart_2036714 baseEnd_2036714 := by
    simpa [prefixWord, tailWord_2036714, baseEnd_2036714] using wordTrace_append hprefix tailTrace_2036714
  have hstable : (prefixWord ++ tailWord_2036714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036714).length < 2 ^ (prefixWord ++ tailWord_2036714).sum := by decide
  have hdescent : baseEnd_2036714 < baseStart_2036714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036759 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_2036759 : Nat := 118140960795 + 2036759 * 2 ^ 59
def prefixEnd_2036759 : Nat := 4983230072969 + 3 ^ 40 * 2036759 * 2
def baseEnd_2036759 : Nat := 464816153053734179886943

theorem tailTrace_2036759 : CollatzResearch.WordTrace tailWord_2036759 prefixEnd_2036759 464816153053734179886943 := by
  unfold tailWord_2036759
  simp only [CollatzResearch.WordTrace]
  refine ⟨74286703628177468588497331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49524469085451645725664887 74286703628177468588497331)
  ·
    refine ⟨111430055442266202882745997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74286703628177468588497331 111430055442266202882745997)
    ·
      refine ⟨41786270790849826081029749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111430055442266202882745997 41786270790849826081029749)
      ·
        refine ⟨3917462886642171195096539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41786270790849826081029749 3917462886642171195096539)
        ·
          refine ⟨5876194329963256792644809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917462886642171195096539 5876194329963256792644809)
          ·
            refine ⟨4407145747472442594483607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5876194329963256792644809 4407145747472442594483607)
            ·
              refine ⟨6610718621208663891725411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407145747472442594483607 6610718621208663891725411)
              ·
                refine ⟨9916077931812995837588117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6610718621208663891725411 9916077931812995837588117)
                ·
                  refine ⟨464816153053734179886943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9916077931812995837588117 464816153053734179886943)
                  ·
                    rfl

theorem cell21_2036759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_2036759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036759 prefixEnd_2036759 := by exact prefixLift 2036759
  have htrace : WordTrace (prefixWord ++ tailWord_2036759) baseStart_2036759 baseEnd_2036759 := by
    simpa [prefixWord, tailWord_2036759, baseEnd_2036759] using wordTrace_append hprefix tailTrace_2036759
  have hstable : (prefixWord ++ tailWord_2036759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036759).length < 2 ^ (prefixWord ++ tailWord_2036759).sum := by decide
  have hdescent : baseEnd_2036759 < baseStart_2036759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036790 : List Nat := [5, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2036790 : Nat := 118140960795 + 2036790 * 2 ^ 59
def prefixEnd_2036790 : Nat := 4983230072969 + 3 ^ 40 * 2036790 * 2
def baseEnd_2036790 : Nat := 154941075892028338290071

theorem tailTrace_2036790 : CollatzResearch.WordTrace tailWord_2036790 prefixEnd_2036790 154941075892028338290071 := by
  unfold tailWord_2036790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642989643191572555179739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49525222860710107255250549 4642989643191572555179739)
  ·
    refine ⟨6964484464787358832769609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4642989643191572555179739 6964484464787358832769609)
    ·
      refine ⟨5223363348590519124577207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6964484464787358832769609 5223363348590519124577207)
      ·
        refine ⟨7835045022885778686865811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223363348590519124577207 7835045022885778686865811)
        ·
          refine ⟨11752567534328668030298717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835045022885778686865811 11752567534328668030298717)
          ·
            refine ⟨4407212825373250511362019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11752567534328668030298717 4407212825373250511362019)
            ·
              refine ⟨6610819238059875767043029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407212825373250511362019 6610819238059875767043029)
              ·
                refine ⟨154941075892028338290071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6610819238059875767043029 154941075892028338290071)
                ·
                  rfl

theorem cell21_2036790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2036790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036790 prefixEnd_2036790 := by exact prefixLift 2036790
  have htrace : WordTrace (prefixWord ++ tailWord_2036790) baseStart_2036790 baseEnd_2036790 := by
    simpa [prefixWord, tailWord_2036790, baseEnd_2036790] using wordTrace_append hprefix tailTrace_2036790
  have hstable : (prefixWord ++ tailWord_2036790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036790).length < 2 ^ (prefixWord ++ tailWord_2036790).sum := by decide
  have hdescent : baseEnd_2036790 < baseStart_2036790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036872 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_2036872 : Nat := 118140960795 + 2036872 * 2 ^ 59
def prefixEnd_2036872 : Nat := 4983230072969 + 3 ^ 40 * 2036872 * 2
def baseEnd_2036872 : Nat := 464841941193271094503379

theorem tailTrace_2036872 : CollatzResearch.WordTrace tailWord_2036872 prefixEnd_2036872 464841941193271094503379 := by
  unfold tailWord_2036872
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145412538384044443680435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49527216717845392591573913 37145412538384044443680435)
  ·
    refine ⟨55718118807576066665520653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37145412538384044443680435 55718118807576066665520653)
    ·
      refine ⟨20894294552841024999570245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55718118807576066665520653 20894294552841024999570245)
      ·
        refine ⟨3917680228657692187419421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20894294552841024999570245 3917680228657692187419421)
        ·
          refine ⟨1469130085746634570282283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3917680228657692187419421 1469130085746634570282283)
          ·
            refine ⟨2203695128619951855423425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469130085746634570282283 2203695128619951855423425)
            ·
              refine ⟨1652771346464963891567569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203695128619951855423425 1652771346464963891567569)
              ·
                refine ⟨1239578509848722918675677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652771346464963891567569 1239578509848722918675677)
                ·
                  refine ⟨464841941193271094503379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239578509848722918675677 464841941193271094503379)
                  ·
                    rfl

theorem cell21_2036872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_2036872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036872 prefixEnd_2036872 := by exact prefixLift 2036872
  have htrace : WordTrace (prefixWord ++ tailWord_2036872) baseStart_2036872 baseEnd_2036872 := by
    simpa [prefixWord, tailWord_2036872, baseEnd_2036872] using wordTrace_append hprefix tailTrace_2036872
  have hstable : (prefixWord ++ tailWord_2036872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036872).length < 2 ^ (prefixWord ++ tailWord_2036872).sum := by decide
  have hdescent : baseEnd_2036872 < baseStart_2036872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036928 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_2036928 : Nat := 118140960795 + 2036928 * 2 ^ 59
def prefixEnd_2036928 : Nat := 4983230072969 + 3 ^ 40 * 2036928 * 2
def baseEnd_2036928 : Nat := 464854721156227441569931

theorem tailTrace_2036928 : CollatzResearch.WordTrace tailWord_2036928 prefixEnd_2036928 464854721156227441569931 := by
  unfold tailWord_2036928
  simp only [CollatzResearch.WordTrace]
  refine ⟨37146433782282605225699719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49528578376376806967599625 37146433782282605225699719)
  ·
    refine ⟨55719650673423907838549579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37146433782282605225699719 55719650673423907838549579)
    ·
      refine ⟨83579476010135861757824369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55719650673423907838549579 83579476010135861757824369)
      ·
        refine ⟨62684607007601896318368277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83579476010135861757824369 62684607007601896318368277)
        ·
          refine ⟨2938340953481338889923513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62684607007601896318368277 2938340953481338889923513)
          ·
            refine ⟨2203755715111004167442635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938340953481338889923513 2203755715111004167442635)
            ·
              refine ⟨3305633572666506251163953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203755715111004167442635 3305633572666506251163953)
              ·
                refine ⟨2479225179499879688372965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3305633572666506251163953 2479225179499879688372965)
                ·
                  refine ⟨464854721156227441569931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479225179499879688372965 464854721156227441569931)
                  ·
                    rfl

theorem cell21_2036928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_2036928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036928 prefixEnd_2036928 := by exact prefixLift 2036928
  have htrace : WordTrace (prefixWord ++ tailWord_2036928) baseStart_2036928 baseEnd_2036928 := by
    simpa [prefixWord, tailWord_2036928, baseEnd_2036928] using wordTrace_append hprefix tailTrace_2036928
  have hstable : (prefixWord ++ tailWord_2036928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036928).length < 2 ^ (prefixWord ++ tailWord_2036928).sum := by decide
  have hdescent : baseEnd_2036928 < baseStart_2036928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036970 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2036970 : Nat := 118140960795 + 2036970 * 2 ^ 59
def prefixEnd_2036970 : Nat := 4983230072969 + 3 ^ 40 * 2036970 * 2
def baseEnd_2036970 : Nat := 464864306128444701869845

theorem tailTrace_2036970 : CollatzResearch.WordTrace tailWord_2036970 prefixEnd_2036970 464864306128444701869845 := by
  unfold tailWord_2036970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573599857603262906107091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49529599620275367749618909 18573599857603262906107091)
  ·
    refine ⟨27860399786404894359160637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18573599857603262906107091 27860399786404894359160637)
    ·
      refine ⟨10447649919901835384685239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27860399786404894359160637 10447649919901835384685239)
      ·
        refine ⟨15671474879852753077027859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10447649919901835384685239 15671474879852753077027859)
        ·
          refine ⟨23507212319779129615541789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671474879852753077027859 23507212319779129615541789)
          ·
            refine ⟨8815204619917173605828171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23507212319779129615541789 8815204619917173605828171)
            ·
              refine ⟨13222806929875760408742257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815204619917173605828171 13222806929875760408742257)
              ·
                refine ⟨9917105197406820306556693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222806929875760408742257 9917105197406820306556693)
                ·
                  refine ⟨464864306128444701869845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9917105197406820306556693 464864306128444701869845)
                  ·
                    rfl

theorem cell21_2036970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2036970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2036970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2036970 prefixEnd_2036970 := by exact prefixLift 2036970
  have htrace : WordTrace (prefixWord ++ tailWord_2036970) baseStart_2036970 baseEnd_2036970 := by
    simpa [prefixWord, tailWord_2036970, baseEnd_2036970] using wordTrace_append hprefix tailTrace_2036970
  have hstable : (prefixWord ++ tailWord_2036970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036970).length < 2 ^ (prefixWord ++ tailWord_2036970).sum := by decide
  have hdescent : baseEnd_2036970 < baseStart_2036970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037004 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_2037004 : Nat := 118140960795 + 2037004 * 2 ^ 59
def prefixEnd_2037004 : Nat := 4983230072969 + 3 ^ 40 * 2037004 * 2
def baseEnd_2037004 : Nat := 464872065391668198303109

theorem tailTrace_2037004 : CollatzResearch.WordTrace tailWord_2037004 prefixEnd_2037004 464872065391668198303109 := by
  unfold tailWord_2037004
  simp only [CollatzResearch.WordTrace]
  refine ⟨37147819756144937715583033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49530426341526583620777377 37147819756144937715583033)
  ·
    refine ⟨27860864817108703286687275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37147819756144937715583033 27860864817108703286687275)
    ·
      refine ⟨41791297225663054930030913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27860864817108703286687275 41791297225663054930030913)
      ·
        refine ⟨31343472919247291197523185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41791297225663054930030913 31343472919247291197523185)
        ·
          refine ⟨23507604689435468398142389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31343472919247291197523185 23507604689435468398142389)
          ·
            refine ⟨2203837939634575162325849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23507604689435468398142389 2203837939634575162325849)
            ·
              refine ⟨1652878454725931371744387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203837939634575162325849 1652878454725931371744387)
              ·
                refine ⟨2479317682088897057616581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652878454725931371744387 2479317682088897057616581)
                ·
                  refine ⟨464872065391668198303109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479317682088897057616581 464872065391668198303109)
                  ·
                    rfl

theorem cell21_2037004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_2037004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037004 prefixEnd_2037004 := by exact prefixLift 2037004
  have htrace : WordTrace (prefixWord ++ tailWord_2037004) baseStart_2037004 baseEnd_2037004 := by
    simpa [prefixWord, tailWord_2037004, baseEnd_2037004] using wordTrace_append hprefix tailTrace_2037004
  have hstable : (prefixWord ++ tailWord_2037004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037004).length < 2 ^ (prefixWord ++ tailWord_2037004).sum := by decide
  have hdescent : baseEnd_2037004 < baseStart_2037004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037015 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_2037015 : Nat := 118140960795 + 2037015 * 2 ^ 59
def prefixEnd_2037015 : Nat := 4983230072969 + 3 ^ 40 * 2037015 * 2
def baseEnd_2037015 : Nat := 464874575741534623619753

theorem tailTrace_2037015 : CollatzResearch.WordTrace tailWord_2037015 prefixEnd_2037015 464874575741534623619753 := by
  unfold tailWord_2037015
  simp only [CollatzResearch.WordTrace]
  refine ⟨74296040715250024309816499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49530693810166682873210999 74296040715250024309816499)
  ·
    refine ⟨111444061072875036464724749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74296040715250024309816499 111444061072875036464724749)
    ·
      refine ⟨41791522902328138674271781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111444061072875036464724749 41791522902328138674271781)
      ·
        refine ⟨7835910544186526001425959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41791522902328138674271781 7835910544186526001425959)
        ·
          refine ⟨11753865816279789002138939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835910544186526001425959 11753865816279789002138939)
          ·
            refine ⟨17630798724419683503208409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11753865816279789002138939 17630798724419683503208409)
            ·
              refine ⟨13223099043314762627406307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17630798724419683503208409 13223099043314762627406307)
              ·
                refine ⟨19834648564972143941109461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13223099043314762627406307 19834648564972143941109461)
                ·
                  refine ⟨464874575741534623619753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19834648564972143941109461 464874575741534623619753)
                  ·
                    rfl

theorem cell21_2037015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_2037015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037015 prefixEnd_2037015 := by exact prefixLift 2037015
  have htrace : WordTrace (prefixWord ++ tailWord_2037015) baseStart_2037015 baseEnd_2037015 := by
    simpa [prefixWord, tailWord_2037015, baseEnd_2037015] using wordTrace_append hprefix tailTrace_2037015
  have hstable : (prefixWord ++ tailWord_2037015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037015).length < 2 ^ (prefixWord ++ tailWord_2037015).sum := by decide
  have hdescent : baseEnd_2037015 < baseStart_2037015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037257 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_2037257 : Nat := 118140960795 + 2037257 * 2 ^ 59
def prefixEnd_2037257 : Nat := 4983230072969 + 3 ^ 40 * 2037257 * 2
def baseEnd_2037257 : Nat := 464929803438595980585925

theorem tailTrace_2037257 : CollatzResearch.WordTrace tailWord_2037257 prefixEnd_2037257 464929803438595980585925 := by
  unfold tailWord_2037257
  simp only [CollatzResearch.WordTrace]
  refine ⟨74304867180373299640126025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49536578120248866426750683 74304867180373299640126025)
  ·
    refine ⟨55728650385279974730094519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74304867180373299640126025 55728650385279974730094519)
    ·
      refine ⟨83592975577919962095141779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55728650385279974730094519 83592975577919962095141779)
      ·
        refine ⟨125389463366879943142712669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83592975577919962095141779 125389463366879943142712669)
        ·
          refine ⟨47021048762579978678517251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125389463366879943142712669 47021048762579978678517251)
          ·
            refine ⟨70531573143869968017775877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47021048762579978678517251 70531573143869968017775877)
            ·
              refine ⟨13224669964475619003332977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70531573143869968017775877 13224669964475619003332977)
              ·
                refine ⟨9918502473356714252499733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13224669964475619003332977 9918502473356714252499733)
                ·
                  refine ⟨464929803438595980585925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9918502473356714252499733 464929803438595980585925)
                  ·
                    rfl

theorem cell21_2037257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_2037257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037257 prefixEnd_2037257 := by exact prefixLift 2037257
  have htrace : WordTrace (prefixWord ++ tailWord_2037257) baseStart_2037257 baseEnd_2037257 := by
    simpa [prefixWord, tailWord_2037257, baseEnd_2037257] using wordTrace_append hprefix tailTrace_2037257
  have hstable : (prefixWord ++ tailWord_2037257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037257).length < 2 ^ (prefixWord ++ tailWord_2037257).sum := by decide
  have hdescent : baseEnd_2037257 < baseStart_2037257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037305 : List Nat := [1, 2, 1, 5, 1, 2, 4, 5]
def baseStart_2037305 : Nat := 118140960795 + 2037305 * 2 ^ 59
def prefixEnd_2037305 : Nat := 4983230072969 + 3 ^ 40 * 2037305 * 2
def baseEnd_2037305 : Nat := 154980252564186187928609

theorem tailTrace_2037305 : CollatzResearch.WordTrace tailWord_2037305 prefixEnd_2037305 154980252564186187928609 := by
  unfold tailWord_2037305
  simp only [CollatzResearch.WordTrace]
  refine ⟨74306617884199403837873369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49537745256132935891915579 74306617884199403837873369)
  ·
    refine ⟨55729963413149552878405027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74306617884199403837873369 55729963413149552878405027)
    ·
      refine ⟨83594945119724329317607541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55729963413149552878405027 83594945119724329317607541)
      ·
        refine ⟨7837026104974155873525707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83594945119724329317607541 7837026104974155873525707)
        ·
          refine ⟨11755539157461233810288561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837026104974155873525707 11755539157461233810288561)
          ·
            refine ⟨8816654368095925357716421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11755539157461233810288561 8816654368095925357716421)
            ·
              refine ⟨1653122694017986004571829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8816654368095925357716421 1653122694017986004571829)
              ·
                refine ⟨154980252564186187928609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1653122694017986004571829 154980252564186187928609)
                ·
                  rfl

theorem cell21_2037305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 5].length) (baseStart_2037305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037305 prefixEnd_2037305 := by exact prefixLift 2037305
  have htrace : WordTrace (prefixWord ++ tailWord_2037305) baseStart_2037305 baseEnd_2037305 := by
    simpa [prefixWord, tailWord_2037305, baseEnd_2037305] using wordTrace_append hprefix tailTrace_2037305
  have hstable : (prefixWord ++ tailWord_2037305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037305).length < 2 ^ (prefixWord ++ tailWord_2037305).sum := by decide
  have hdescent : baseEnd_2037305 < baseStart_2037305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037384 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_2037384 : Nat := 118140960795 + 2037384 * 2 ^ 59
def prefixEnd_2037384 : Nat := 4983230072969 + 3 ^ 40 * 2037384 * 2
def baseEnd_2037384 : Nat := 464958786568871981968999

theorem tailTrace_2037384 : CollatzResearch.WordTrace tailWord_2037384 prefixEnd_2037384 464958786568871981968999 := by
  unfold tailWord_2037384
  simp only [CollatzResearch.WordTrace]
  refine ⟨37154749625456600164999603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49539666167275466886666137 37154749625456600164999603)
  ·
    refine ⟨55732124438184900247499405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37154749625456600164999603 55732124438184900247499405)
    ·
      refine ⟨20899546664319337592812277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55732124438184900247499405 20899546664319337592812277)
      ·
        refine ⟨1959332499779937899326151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20899546664319337592812277 1959332499779937899326151)
        ·
          refine ⟨2938998749669906848989227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959332499779937899326151 2938998749669906848989227)
          ·
            refine ⟨4408498124504860273483841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938998749669906848989227 4408498124504860273483841)
            ·
              refine ⟨3306373593378645205112881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408498124504860273483841 3306373593378645205112881)
              ·
                refine ⟨2479780195033983903834661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306373593378645205112881 2479780195033983903834661)
                ·
                  refine ⟨464958786568871981968999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479780195033983903834661 464958786568871981968999)
                  ·
                    rfl

theorem cell21_2037384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_2037384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037384 prefixEnd_2037384 := by exact prefixLift 2037384
  have htrace : WordTrace (prefixWord ++ tailWord_2037384) baseStart_2037384 baseEnd_2037384 := by
    simpa [prefixWord, tailWord_2037384, baseEnd_2037384] using wordTrace_append hprefix tailTrace_2037384
  have hstable : (prefixWord ++ tailWord_2037384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037384).length < 2 ^ (prefixWord ++ tailWord_2037384).sum := by decide
  have hdescent : baseEnd_2037384 < baseStart_2037384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037446 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2037446 : Nat := 118140960795 + 2037446 * 2 ^ 59
def prefixEnd_2037446 : Nat := 4983230072969 + 3 ^ 40 * 2037446 * 2
def baseEnd_2037446 : Nat := 464972935813573651935539

theorem tailTrace_2037446 : CollatzResearch.WordTrace tailWord_2037446 prefixEnd_2037446 464972935813573651935539 := by
  unfold tailWord_2037446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322242518021518278711131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49541173717792389945837461 2322242518021518278711131)
  ·
    refine ⟨3483363777032277418066697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322242518021518278711131 3483363777032277418066697)
    ·
      refine ⟨2612522832774208063550023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3483363777032277418066697 2612522832774208063550023)
      ·
        refine ⟨3918784249161312095325035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612522832774208063550023 3918784249161312095325035)
        ·
          refine ⟨5878176373741968142987553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918784249161312095325035 5878176373741968142987553)
          ·
            refine ⟨4408632280306476107240665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878176373741968142987553 4408632280306476107240665)
            ·
              refine ⟨3306474210229857080430499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408632280306476107240665 3306474210229857080430499)
              ·
                refine ⟨4959711315344785620645749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306474210229857080430499 4959711315344785620645749)
                ·
                  refine ⟨464972935813573651935539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4959711315344785620645749 464972935813573651935539)
                  ·
                    rfl

theorem cell21_2037446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2037446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037446 prefixEnd_2037446 := by exact prefixLift 2037446
  have htrace : WordTrace (prefixWord ++ tailWord_2037446) baseStart_2037446 baseEnd_2037446 := by
    simpa [prefixWord, tailWord_2037446, baseEnd_2037446] using wordTrace_append hprefix tailTrace_2037446
  have hstable : (prefixWord ++ tailWord_2037446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037446).length < 2 ^ (prefixWord ++ tailWord_2037446).sum := by decide
  have hdescent : baseEnd_2037446 < baseStart_2037446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037460 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2037460 : Nat := 118140960795 + 2037460 * 2 ^ 59
def prefixEnd_2037460 : Nat := 4983230072969 + 3 ^ 40 * 2037460 * 2
def baseEnd_2037460 : Nat := 464976130804312738702177

theorem tailTrace_2037460 : CollatzResearch.WordTrace tailWord_2037460 prefixEnd_2037460 464976130804312738702177 := by
  unfold tailWord_2037460
  simp only [CollatzResearch.WordTrace]
  refine ⟨37156135599318932654882917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49541514132425243539843889 37156135599318932654882917)
  ·
    refine ⟨6966775424872299872790547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37156135599318932654882917 6966775424872299872790547)
    ·
      refine ⟨10450163137308449809185821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6966775424872299872790547 10450163137308449809185821)
      ·
        refine ⟨3918811176490668678444683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10450163137308449809185821 3918811176490668678444683)
        ·
          refine ⟨5878216764736003017667025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918811176490668678444683 5878216764736003017667025)
          ·
            refine ⟨4408662573552002263250269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878216764736003017667025 4408662573552002263250269)
            ·
              refine ⟨1653248465082000848718851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4408662573552002263250269 1653248465082000848718851)
              ·
                refine ⟨2479872697623001273078277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653248465082000848718851 2479872697623001273078277)
                ·
                  refine ⟨464976130804312738702177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2479872697623001273078277 464976130804312738702177)
                  ·
                    rfl

theorem cell21_2037460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2037460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037460 prefixEnd_2037460 := by exact prefixLift 2037460
  have htrace : WordTrace (prefixWord ++ tailWord_2037460) baseStart_2037460 baseEnd_2037460 := by
    simpa [prefixWord, tailWord_2037460, baseEnd_2037460] using wordTrace_append hprefix tailTrace_2037460
  have hstable : (prefixWord ++ tailWord_2037460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037460).length < 2 ^ (prefixWord ++ tailWord_2037460).sum := by decide
  have hdescent : baseEnd_2037460 < baseStart_2037460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037668 : List Nat := [2, 3, 1, 2, 1, 5, 7]
def baseStart_2037668 : Nat := 118140960795 + 2037668 * 2 ^ 59
def prefixEnd_2037668 : Nat := 4983230072969 + 3 ^ 40 * 2037668 * 2
def baseEnd_2037668 : Nat := 51669288804238955470565

theorem tailTrace_2037668 : CollatzResearch.WordTrace tailWord_2037668 prefixEnd_2037668 51669288804238955470565 := by
  unfold tailWord_2037668
  simp only [CollatzResearch.WordTrace]
  refine ⟨37159928790942158416668829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49546571721256211222225105 37159928790942158416668829)
  ·
    refine ⟨13934973296603309406250811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37159928790942158416668829 13934973296603309406250811)
    ·
      refine ⟨20902459944904964109376217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13934973296603309406250811 20902459944904964109376217)
      ·
        refine ⟨15676844958678723082032163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20902459944904964109376217 15676844958678723082032163)
        ·
          refine ⟨23515267438018084623048245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15676844958678723082032163 23515267438018084623048245)
          ·
            refine ⟨2204556322314195433410773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23515267438018084623048245 2204556322314195433410773)
            ·
              refine ⟨51669288804238955470565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2204556322314195433410773 51669288804238955470565)
              ·
                rfl

theorem cell21_2037668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 7].length) (baseStart_2037668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037668 prefixEnd_2037668 := by exact prefixLift 2037668
  have htrace : WordTrace (prefixWord ++ tailWord_2037668) baseStart_2037668 baseEnd_2037668 := by
    simpa [prefixWord, tailWord_2037668, baseEnd_2037668] using wordTrace_append hprefix tailTrace_2037668
  have hstable : (prefixWord ++ tailWord_2037668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037668).length < 2 ^ (prefixWord ++ tailWord_2037668).sum := by decide
  have hdescent : baseEnd_2037668 < baseStart_2037668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037716 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2037716 : Nat := 118140960795 + 2037716 * 2 ^ 59
def prefixEnd_2037716 : Nat := 4983230072969 + 3 ^ 40 * 2037716 * 2
def baseEnd_2037716 : Nat := 465034553492113182434987

theorem tailTrace_2037716 : CollatzResearch.WordTrace tailWord_2037716 prefixEnd_2037716 465034553492113182434987 := by
  unfold tailWord_2037716
  simp only [CollatzResearch.WordTrace]
  refine ⟨37160804142855210515542501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49547738857140280687390001 37160804142855210515542501)
  ·
    refine ⟨6967650776785351971664219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37160804142855210515542501 6967650776785351971664219)
    ·
      refine ⟨10451476165178027957496329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967650776785351971664219 10451476165178027957496329)
      ·
        refine ⟨7838607123883520968122247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10451476165178027957496329 7838607123883520968122247)
        ·
          refine ⟨11757910685825281452183371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838607123883520968122247 11757910685825281452183371)
          ·
            refine ⟨17636866028737922178275057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757910685825281452183371 17636866028737922178275057)
            ·
              refine ⟨13227649521553441633706293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17636866028737922178275057 13227649521553441633706293)
              ·
                refine ⟨1240092142645635153159965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13227649521553441633706293 1240092142645635153159965)
                ·
                  refine ⟨465034553492113182434987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240092142645635153159965 465034553492113182434987)
                  ·
                    rfl

theorem cell21_2037716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2037716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037716 prefixEnd_2037716 := by exact prefixLift 2037716
  have htrace : WordTrace (prefixWord ++ tailWord_2037716) baseStart_2037716 baseEnd_2037716 := by
    simpa [prefixWord, tailWord_2037716, baseEnd_2037716] using wordTrace_append hprefix tailTrace_2037716
  have hstable : (prefixWord ++ tailWord_2037716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037716).length < 2 ^ (prefixWord ++ tailWord_2037716).sum := by decide
  have hdescent : baseEnd_2037716 < baseStart_2037716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037727 : List Nat := [1, 1, 2, 3, 4, 10]
def baseStart_2037727 : Nat := 118140960795 + 2037727 * 2 ^ 59
def prefixEnd_2037727 : Nat := 4983230072969 + 3 ^ 40 * 2037727 * 2
def baseEnd_2037727 : Nat := 17223594957110355842653

theorem tailTrace_2037727 : CollatzResearch.WordTrace tailWord_2037727 prefixEnd_2037727 17223594957110355842653 := by
  unfold tailWord_2037727
  simp only [CollatzResearch.WordTrace]
  refine ⟨74322009488670569909735435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49548006325780379939823623 74322009488670569909735435)
  ·
    refine ⟨111483014233005854864603153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74322009488670569909735435 111483014233005854864603153)
    ·
      refine ⟨83612260674754391148452365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111483014233005854864603153 83612260674754391148452365)
      ·
        refine ⟨31354597753032896680669637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83612260674754391148452365 31354597753032896680669637)
        ·
          refine ⟨5878987078693668127625557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31354597753032896680669637 5878987078693668127625557)
          ·
            refine ⟨17223594957110355842653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5878987078693668127625557 17223594957110355842653)
            ·
              rfl

theorem cell21_2037727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 10].length) (baseStart_2037727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037727 prefixEnd_2037727 := by exact prefixLift 2037727
  have htrace : WordTrace (prefixWord ++ tailWord_2037727) baseStart_2037727 baseEnd_2037727 := by
    simpa [prefixWord, tailWord_2037727, baseEnd_2037727] using wordTrace_append hprefix tailTrace_2037727
  have hstable : (prefixWord ++ tailWord_2037727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037727).length < 2 ^ (prefixWord ++ tailWord_2037727).sum := by decide
  have hdescent : baseEnd_2037727 < baseStart_2037727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037865 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_2037865 : Nat := 118140960795 + 2037865 * 2 ^ 59
def prefixEnd_2037865 : Nat := 4983230072969 + 3 ^ 40 * 2037865 * 2
def baseEnd_2037865 : Nat := 465068557322122034451349

theorem tailTrace_2037865 : CollatzResearch.WordTrace tailWord_2037865 prefixEnd_2037865 465068557322122034451349 := by
  unfold tailWord_2037865
  simp only [CollatzResearch.WordTrace]
  refine ⟨74327042762170619478259049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49551361841447079652172699 74327042762170619478259049)
  ·
    refine ⟨55745282071627964608694287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74327042762170619478259049 55745282071627964608694287)
    ·
      refine ⟨83617923107441946913041431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55745282071627964608694287 83617923107441946913041431)
      ·
        refine ⟨125426884661162920369562147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83617923107441946913041431 125426884661162920369562147)
        ·
          refine ⟨188140326991744380554343221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125426884661162920369562147 188140326991744380554343221)
          ·
            refine ⟨17638155655476035676969677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188140326991744380554343221 17638155655476035676969677)
            ·
              refine ⟨6614308370803513378863629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17638155655476035676969677 6614308370803513378863629)
              ·
                refine ⟨2480365639051317517073861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6614308370803513378863629 2480365639051317517073861)
                ·
                  refine ⟨465068557322122034451349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480365639051317517073861 465068557322122034451349)
                  ·
                    rfl

theorem cell21_2037865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_2037865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037865 prefixEnd_2037865 := by exact prefixLift 2037865
  have htrace : WordTrace (prefixWord ++ tailWord_2037865) baseStart_2037865 baseEnd_2037865 := by
    simpa [prefixWord, tailWord_2037865, baseEnd_2037865] using wordTrace_append hprefix tailTrace_2037865
  have hstable : (prefixWord ++ tailWord_2037865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037865).length < 2 ^ (prefixWord ++ tailWord_2037865).sum := by decide
  have hdescent : baseEnd_2037865 < baseStart_2037865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037879 : List Nat := [1, 1, 3, 1, 1, 5, 2, 7]
def baseStart_2037879 : Nat := 118140960795 + 2037879 * 2 ^ 59
def prefixEnd_2037879 : Nat := 4983230072969 + 3 ^ 40 * 2037879 * 2
def baseEnd_2037879 : Nat := 155023917437620373739329

theorem tailTrace_2037879 : CollatzResearch.WordTrace tailWord_2037879 prefixEnd_2037879 155023917437620373739329 := by
  unfold tailWord_2037879
  simp only [CollatzResearch.WordTrace]
  refine ⟨74327553384119899869268691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49551702256079933246179127 74327553384119899869268691)
  ·
    refine ⟨111491330076179849803903037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74327553384119899869268691 111491330076179849803903037)
    ·
      refine ⟨41809248778567443676463639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111491330076179849803903037 41809248778567443676463639)
      ·
        refine ⟨62713873167851165514695459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41809248778567443676463639 62713873167851165514695459)
        ·
          refine ⟨94070809751776748272043189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62713873167851165514695459 94070809751776748272043189)
          ·
            refine ⟨8819138414229070150504049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94070809751776748272043189 8819138414229070150504049)
            ·
              refine ⟨6614353810671802612878037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8819138414229070150504049 6614353810671802612878037)
              ·
                refine ⟨155023917437620373739329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6614353810671802612878037 155023917437620373739329)
                ·
                  rfl

theorem cell21_2037879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_2037879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037879 prefixEnd_2037879 := by exact prefixLift 2037879
  have htrace : WordTrace (prefixWord ++ tailWord_2037879) baseStart_2037879 baseEnd_2037879 := by
    simpa [prefixWord, tailWord_2037879, baseEnd_2037879] using wordTrace_append hprefix tailTrace_2037879
  have hstable : (prefixWord ++ tailWord_2037879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037879).length < 2 ^ (prefixWord ++ tailWord_2037879).sum := by decide
  have hdescent : baseEnd_2037879 < baseStart_2037879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037902 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_2037902 : Nat := 118140960795 + 2037902 * 2 ^ 59
def prefixEnd_2037902 : Nat := 4983230072969 + 3 ^ 40 * 2037902 * 2
def baseEnd_2037902 : Nat := 465077001226218192334607

theorem tailTrace_2037902 : CollatzResearch.WordTrace tailWord_2037902 prefixEnd_2037902 465077001226218192334607 := by
  unfold tailWord_2037902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9291049032879571849669495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49552261508691049864903973 9291049032879571849669495)
  ·
    refine ⟨13936573549319357774504243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9291049032879571849669495 13936573549319357774504243)
    ·
      refine ⟨20904860323979036661756365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13936573549319357774504243 20904860323979036661756365)
      ·
        refine ⟨7839322621492138748158637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20904860323979036661756365 7839322621492138748158637)
        ·
          refine ⟨2939745983059552030559489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7839322621492138748158637 2939745983059552030559489)
          ·
            refine ⟨2204809487294664022919617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939745983059552030559489 2204809487294664022919617)
            ·
              refine ⟨1653607115470998017189713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204809487294664022919617 1653607115470998017189713)
              ·
                refine ⟨1240205336603248512892285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653607115470998017189713 1240205336603248512892285)
                ·
                  refine ⟨465077001226218192334607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240205336603248512892285 465077001226218192334607)
                  ·
                    rfl

theorem cell21_2037902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_2037902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037902 prefixEnd_2037902 := by exact prefixLift 2037902
  have htrace : WordTrace (prefixWord ++ tailWord_2037902) baseStart_2037902 baseEnd_2037902 := by
    simpa [prefixWord, tailWord_2037902, baseEnd_2037902] using wordTrace_append hprefix tailTrace_2037902
  have hstable : (prefixWord ++ tailWord_2037902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037902).length < 2 ^ (prefixWord ++ tailWord_2037902).sum := by decide
  have hdescent : baseEnd_2037902 < baseStart_2037902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037930 : List Nat := [3, 1, 5, 1, 2, 1, 3, 5]
def baseStart_2037930 : Nat := 118140960795 + 2037930 * 2 ^ 59
def prefixEnd_2037930 : Nat := 4983230072969 + 3 ^ 40 * 2037930 * 2
def baseEnd_2037930 : Nat := 155027797069232121955961

theorem tailTrace_2037930 : CollatzResearch.WordTrace tailWord_2037930 prefixEnd_2037930 155027797069232121955961 := by
  unfold tailWord_2037930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582353376733783894843811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49552942337956757052916829 18582353376733783894843811)
  ·
    refine ⟨27873530065100675842265717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582353376733783894843811 27873530065100675842265717)
    ·
      refine ⟨2613143443603188360212411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27873530065100675842265717 2613143443603188360212411)
      ·
        refine ⟨3919715165404782540318617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613143443603188360212411 3919715165404782540318617)
        ·
          refine ⟨2939786374053586905238963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3919715165404782540318617 2939786374053586905238963)
          ·
            refine ⟨4409679561080380357858445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939786374053586905238963 4409679561080380357858445)
            ·
              refine ⟨1653629835405142634196917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409679561080380357858445 1653629835405142634196917)
              ·
                refine ⟨155027797069232121955961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1653629835405142634196917 155027797069232121955961)
                ·
                  rfl

theorem cell21_2037930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_2037930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037930 prefixEnd_2037930 := by exact prefixLift 2037930
  have htrace : WordTrace (prefixWord ++ tailWord_2037930) baseStart_2037930 baseEnd_2037930 := by
    simpa [prefixWord, tailWord_2037930, baseEnd_2037930] using wordTrace_append hprefix tailTrace_2037930
  have hstable : (prefixWord ++ tailWord_2037930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037930).length < 2 ^ (prefixWord ++ tailWord_2037930).sum := by decide
  have hdescent : baseEnd_2037930 < baseStart_2037930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037989 : List Nat := [1, 3, 1, 4, 2, 3, 2, 5]
def baseStart_2037989 : Nat := 118140960795 + 2037989 * 2 ^ 59
def prefixEnd_2037989 : Nat := 4983230072969 + 3 ^ 40 * 2037989 * 2
def baseEnd_2037989 : Nat := 155032285270508458128143

theorem tailTrace_2037989 : CollatzResearch.WordTrace tailWord_2037989 prefixEnd_2037989 155032285270508458128143 := by
  unfold tailWord_2037989
  simp only [CollatzResearch.WordTrace]
  refine ⟨74331565413721388655773021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49554376942480925770515347 74331565413721388655773021)
  ·
    refine ⟨27874337030145520745914883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74331565413721388655773021 27874337030145520745914883)
    ·
      refine ⟨41811505545218281118872325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27874337030145520745914883 41811505545218281118872325)
      ·
        refine ⟨7839657289728427709788561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41811505545218281118872325 7839657289728427709788561)
        ·
          refine ⟨5879742967296320782341421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7839657289728427709788561 5879742967296320782341421)
          ·
            refine ⟨2204903612736120293378033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5879742967296320782341421 2204903612736120293378033)
            ·
              refine ⟨1653677709552090220033525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204903612736120293378033 1653677709552090220033525)
              ·
                refine ⟨155032285270508458128143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1653677709552090220033525 155032285270508458128143)
                ·
                  rfl

theorem cell21_2037989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 5].length) (baseStart_2037989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2037989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2037989 prefixEnd_2037989 := by exact prefixLift 2037989
  have htrace : WordTrace (prefixWord ++ tailWord_2037989) baseStart_2037989 baseEnd_2037989 := by
    simpa [prefixWord, tailWord_2037989, baseEnd_2037989] using wordTrace_append hprefix tailTrace_2037989
  have hstable : (prefixWord ++ tailWord_2037989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037989).length < 2 ^ (prefixWord ++ tailWord_2037989).sum := by decide
  have hdescent : baseEnd_2037989 < baseStart_2037989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038017 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_2038017 : Nat := 118140960795 + 2038017 * 2 ^ 59
def prefixEnd_2038017 : Nat := 4983230072969 + 3 ^ 40 * 2038017 * 2
def baseEnd_2038017 : Nat := 465103245793003547917705

theorem tailTrace_2038017 : CollatzResearch.WordTrace tailWord_2038017 prefixEnd_2038017 465103245793003547917705 := by
  unfold tailWord_2038017
  simp only [CollatzResearch.WordTrace]
  refine ⟨74332586657619949437792305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49555057771746632958528203 74332586657619949437792305)
  ·
    refine ⟨55749439993214962078344229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74332586657619949437792305 55749439993214962078344229)
    ·
      refine ⟨10453019998727805389689543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55749439993214962078344229 10453019998727805389689543)
      ·
        refine ⟨15679529998091708084534315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453019998727805389689543 15679529998091708084534315)
        ·
          refine ⟨23519294997137562126801473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679529998091708084534315 23519294997137562126801473)
          ·
            refine ⟨17639471247853171595101105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23519294997137562126801473 17639471247853171595101105)
            ·
              refine ⟨13229603435889878696325829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17639471247853171595101105 13229603435889878696325829)
              ·
                refine ⟨2480550644229352255561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13229603435889878696325829 2480550644229352255561093)
                ·
                  refine ⟨465103245793003547917705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2480550644229352255561093 465103245793003547917705)
                  ·
                    rfl

theorem cell21_2038017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_2038017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038017 prefixEnd_2038017 := by exact prefixLift 2038017
  have htrace : WordTrace (prefixWord ++ tailWord_2038017) baseStart_2038017 baseEnd_2038017 := by
    simpa [prefixWord, tailWord_2038017, baseEnd_2038017] using wordTrace_append hprefix tailTrace_2038017
  have hstable : (prefixWord ++ tailWord_2038017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038017).length < 2 ^ (prefixWord ++ tailWord_2038017).sum := by decide
  have hdescent : baseEnd_2038017 < baseStart_2038017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038020 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2038020 : Nat := 118140960795 + 2038020 * 2 ^ 59
def prefixEnd_2038020 : Nat := 4983230072969 + 3 ^ 40 * 2038020 * 2
def baseEnd_2038020 : Nat := 465103930433876209367699

theorem tailTrace_2038020 : CollatzResearch.WordTrace tailWord_2038020 prefixEnd_2038020 465103930433876209367699 := by
  unfold tailWord_2038020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37166348038304540475075757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49555130717739387300101009 37166348038304540475075757)
  ·
    refine ⟨13937380514364202678153409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37166348038304540475075757 13937380514364202678153409)
    ·
      refine ⟨10453035385773152008615057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13937380514364202678153409 10453035385773152008615057)
      ·
        refine ⟨7839776539329864006461293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10453035385773152008615057 7839776539329864006461293)
        ·
          refine ⟨2939916202248699002422985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7839776539329864006461293 2939916202248699002422985)
          ·
            refine ⟨2204937151686524251817239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939916202248699002422985 2204937151686524251817239)
            ·
              refine ⟨3307405727529786377725859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204937151686524251817239 3307405727529786377725859)
              ·
                refine ⟨4961108591294679566588789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307405727529786377725859 4961108591294679566588789)
                ·
                  refine ⟨465103930433876209367699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961108591294679566588789 465103930433876209367699)
                  ·
                    rfl

theorem cell21_2038020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2038020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038020 prefixEnd_2038020 := by exact prefixLift 2038020
  have htrace : WordTrace (prefixWord ++ tailWord_2038020) baseStart_2038020 baseEnd_2038020 := by
    simpa [prefixWord, tailWord_2038020, baseEnd_2038020] using wordTrace_append hprefix tailTrace_2038020
  have hstable : (prefixWord ++ tailWord_2038020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038020).length < 2 ^ (prefixWord ++ tailWord_2038020).sum := by decide
  have hdescent : baseEnd_2038020 < baseStart_2038020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038079 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 3]
def baseStart_2038079 : Nat := 118140960795 + 2038079 * 2 ^ 59
def prefixEnd_2038079 : Nat := 4983230072969 + 3 ^ 40 * 2038079 * 2
def baseEnd_2038079 : Nat := 465117395037705217884245

theorem tailTrace_2038079 : CollatzResearch.WordTrace tailWord_2038079 prefixEnd_2038079 465117395037705217884245 := by
  unfold tailWord_2038079
  simp only [CollatzResearch.WordTrace]
  refine ⟨74334847983395334026549291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49556565322263556017699527 74334847983395334026549291)
  ·
    refine ⟨111502271975093001039823937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74334847983395334026549291 111502271975093001039823937)
    ·
      refine ⟨83626703981319750779867953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111502271975093001039823937 83626703981319750779867953)
      ·
        refine ⟨62720027985989813084900965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83626703981319750779867953 62720027985989813084900965)
        ·
          refine ⟨11760005247373089953418931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62720027985989813084900965 11760005247373089953418931)
          ·
            refine ⟨17640007871059634930128397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760005247373089953418931 17640007871059634930128397)
            ·
              refine ⟨6615002951647363098798149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17640007871059634930128397 6615002951647363098798149)
              ·
                refine ⟨1240313053433880581024653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6615002951647363098798149 1240313053433880581024653)
                ·
                  refine ⟨465117395037705217884245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240313053433880581024653 465117395037705217884245)
                  ·
                    rfl

theorem cell21_2038079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3].length) (baseStart_2038079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038079 prefixEnd_2038079 := by exact prefixLift 2038079
  have htrace : WordTrace (prefixWord ++ tailWord_2038079) baseStart_2038079 baseEnd_2038079 := by
    simpa [prefixWord, tailWord_2038079, baseEnd_2038079] using wordTrace_append hprefix tailTrace_2038079
  have hstable : (prefixWord ++ tailWord_2038079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038079).length < 2 ^ (prefixWord ++ tailWord_2038079).sum := by decide
  have hdescent : baseEnd_2038079 < baseStart_2038079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038121 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_2038121 : Nat := 118140960795 + 2038121 * 2 ^ 59
def prefixEnd_2038121 : Nat := 4983230072969 + 3 ^ 40 * 2038121 * 2
def baseEnd_2038121 : Nat := 465126980009922478184159

theorem tailTrace_2038121 : CollatzResearch.WordTrace tailWord_2038121 prefixEnd_2038121 465126980009922478184159 := by
  unfold tailWord_2038121
  simp only [CollatzResearch.WordTrace]
  refine ⟨74336379849243175199578217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49557586566162116799718811 74336379849243175199578217)
  ·
    refine ⟨55752284886932381399683663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74336379849243175199578217 55752284886932381399683663)
    ·
      refine ⟨83628427330398572099525495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55752284886932381399683663 83628427330398572099525495)
      ·
        refine ⟨125442640995597858149288243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83628427330398572099525495 125442640995597858149288243)
        ·
          refine ⟨188163961493396787223932365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125442640995597858149288243 188163961493396787223932365)
          ·
            refine ⟨70561485560023795208974637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188163961493396787223932365 70561485560023795208974637)
            ·
              refine ⟨26460557085008923203365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70561485560023795208974637 26460557085008923203365489)
              ·
                refine ⟨19845417813756692402524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26460557085008923203365489 19845417813756692402524117)
                ·
                  refine ⟨465126980009922478184159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19845417813756692402524117 465126980009922478184159)
                  ·
                    rfl

theorem cell21_2038121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_2038121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038121 prefixEnd_2038121 := by exact prefixLift 2038121
  have htrace : WordTrace (prefixWord ++ tailWord_2038121) baseStart_2038121 baseEnd_2038121 := by
    simpa [prefixWord, tailWord_2038121, baseEnd_2038121] using wordTrace_append hprefix tailTrace_2038121
  have hstable : (prefixWord ++ tailWord_2038121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038121).length < 2 ^ (prefixWord ++ tailWord_2038121).sum := by decide
  have hdescent : baseEnd_2038121 < baseStart_2038121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038183 : List Nat := [1, 1, 6, 1, 1, 2, 9]
def baseStart_2038183 : Nat := 118140960795 + 2038183 * 2 ^ 59
def prefixEnd_2038183 : Nat := 4983230072969 + 3 ^ 40 * 2038183 * 2
def baseEnd_2038183 : Nat := 51682347694958238683411

theorem tailTrace_2038183 : CollatzResearch.WordTrace tailWord_2038183 prefixEnd_2038183 51682347694958238683411 := by
  unfold tailWord_2038183
  simp only [CollatzResearch.WordTrace]
  refine ⟨74338641175018559788335203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49559094116679039858890135 74338641175018559788335203)
  ·
    refine ⟨111507961762527839682502805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74338641175018559788335203 111507961762527839682502805)
    ·
      refine ⟨5226935707618492485117319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111507961762527839682502805 5226935707618492485117319)
      ·
        refine ⟨7840403561427738727675979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226935707618492485117319 7840403561427738727675979)
        ·
          refine ⟨11760605342141608091513969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840403561427738727675979 11760605342141608091513969)
          ·
            refine ⟨8820454006606206068635477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11760605342141608091513969 8820454006606206068635477)
            ·
              refine ⟨51682347694958238683411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8820454006606206068635477 51682347694958238683411)
              ·
                rfl

theorem cell21_2038183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 9].length) (baseStart_2038183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038183 prefixEnd_2038183 := by exact prefixLift 2038183
  have htrace : WordTrace (prefixWord ++ tailWord_2038183) baseStart_2038183 baseEnd_2038183 := by
    simpa [prefixWord, tailWord_2038183, baseEnd_2038183] using wordTrace_append hprefix tailTrace_2038183
  have hstable : (prefixWord ++ tailWord_2038183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038183).length < 2 ^ (prefixWord ++ tailWord_2038183).sum := by decide
  have hdescent : baseEnd_2038183 < baseStart_2038183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038189 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2038189 : Nat := 118140960795 + 2038189 * 2 ^ 59
def prefixEnd_2038189 : Nat := 4983230072969 + 3 ^ 40 * 2038189 * 2
def baseEnd_2038189 : Nat := 465142498536369471050687

theorem tailTrace_2038189 : CollatzResearch.WordTrace tailWord_2038189 prefixEnd_2038189 465142498536369471050687 := by
  unfold tailWord_2038189
  simp only [CollatzResearch.WordTrace]
  refine ⟨74338860012996822813053621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49559240008664548542035747 74338860012996822813053621)
  ·
    refine ⟨6969268126218452138723777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74338860012996822813053621 6969268126218452138723777)
    ·
      refine ⟨5226951094663839104042833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6969268126218452138723777 5226951094663839104042833)
      ·
        refine ⟨3920213320997879328032125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5226951094663839104042833 3920213320997879328032125)
        ·
          refine ⟨1470079995374204748012047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3920213320997879328032125 1470079995374204748012047)
          ·
            refine ⟨2205119993061307122018071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470079995374204748012047 2205119993061307122018071)
            ·
              refine ⟨3307679989591960683027107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205119993061307122018071 3307679989591960683027107)
              ·
                refine ⟨4961519984387941024540661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307679989591960683027107 4961519984387941024540661)
                ·
                  refine ⟨465142498536369471050687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961519984387941024540661 465142498536369471050687)
                  ·
                    rfl

theorem cell21_2038189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2038189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038189 prefixEnd_2038189 := by exact prefixLift 2038189
  have htrace : WordTrace (prefixWord ++ tailWord_2038189) baseStart_2038189 baseEnd_2038189 := by
    simpa [prefixWord, tailWord_2038189, baseEnd_2038189] using wordTrace_append hprefix tailTrace_2038189
  have hstable : (prefixWord ++ tailWord_2038189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038189).length < 2 ^ (prefixWord ++ tailWord_2038189).sum := by decide
  have hdescent : baseEnd_2038189 < baseStart_2038189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038248 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_2038248 : Nat := 118140960795 + 2038248 * 2 ^ 59
def prefixEnd_2038248 : Nat := 4983230072969 + 3 ^ 40 * 2038248 * 2
def baseEnd_2038248 : Nat := 465155963140198479567233

theorem tailTrace_2038248 : CollatzResearch.WordTrace tailWord_2038248 prefixEnd_2038248 465155963140198479567233 := by
  unfold tailWord_2038248
  simp only [CollatzResearch.WordTrace]
  refine ⟨37170505959891537944725699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49560674613188717259634265 37170505959891537944725699)
  ·
    refine ⟨55755758939837306917088549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37170505959891537944725699 55755758939837306917088549)
    ·
      refine ⟨10454204801219495046954103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55755758939837306917088549 10454204801219495046954103)
      ·
        refine ⟨15681307201829242570431155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454204801219495046954103 15681307201829242570431155)
        ·
          refine ⟨23521960802743863855646733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681307201829242570431155 23521960802743863855646733)
          ·
            refine ⟨8820735301028948945867525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23521960802743863855646733 8820735301028948945867525)
            ·
              refine ⟨1653887868942927927350161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8820735301028948945867525 1653887868942927927350161)
              ·
                refine ⟨1240415901707195945512621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653887868942927927350161 1240415901707195945512621)
                ·
                  refine ⟨465155963140198479567233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240415901707195945512621 465155963140198479567233)
                  ·
                    rfl

theorem cell21_2038248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_2038248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038248 prefixEnd_2038248 := by exact prefixLift 2038248
  have htrace : WordTrace (prefixWord ++ tailWord_2038248) baseStart_2038248 baseEnd_2038248 := by
    simpa [prefixWord, tailWord_2038248, baseEnd_2038248] using wordTrace_append hprefix tailTrace_2038248
  have hstable : (prefixWord ++ tailWord_2038248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038248).length < 2 ^ (prefixWord ++ tailWord_2038248).sum := by decide
  have hdescent : baseEnd_2038248 < baseStart_2038248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038307 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 3]
def baseStart_2038307 : Nat := 118140960795 + 2038307 * 2 ^ 59
def prefixEnd_2038307 : Nat := 4983230072969 + 3 ^ 40 * 2038307 * 2
def baseEnd_2038307 : Nat := 465169427744027488083779

theorem tailTrace_2038307 : CollatzResearch.WordTrace tailWord_2038307 prefixEnd_2038307 465169427744027488083779 := by
  unfold tailWord_2038307
  simp only [CollatzResearch.WordTrace]
  refine ⟨74343163826569328965849175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49562109217712885977232783 74343163826569328965849175)
  ·
    refine ⟨111514745739853993448773763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74343163826569328965849175 111514745739853993448773763)
    ·
      refine ⟨167272118609780990173160645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111514745739853993448773763 167272118609780990173160645)
      ·
        refine ⟨31363522239333935657467621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167272118609780990173160645 31363522239333935657467621)
        ·
          refine ⟨5880660419875112935775179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31363522239333935657467621 5880660419875112935775179)
          ·
            refine ⟨8820990629812669403662769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880660419875112935775179 8820990629812669403662769)
            ·
              refine ⟨6615742972359502052747077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8820990629812669403662769 6615742972359502052747077)
              ·
                refine ⟨1240451807317406634890077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6615742972359502052747077 1240451807317406634890077)
                ·
                  refine ⟨465169427744027488083779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240451807317406634890077 465169427744027488083779)
                  ·
                    rfl

theorem cell21_2038307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3].length) (baseStart_2038307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038307 prefixEnd_2038307 := by exact prefixLift 2038307
  have htrace : WordTrace (prefixWord ++ tailWord_2038307) baseStart_2038307 baseEnd_2038307 := by
    simpa [prefixWord, tailWord_2038307, baseEnd_2038307] using wordTrace_append hprefix tailTrace_2038307
  have hstable : (prefixWord ++ tailWord_2038307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038307).length < 2 ^ (prefixWord ++ tailWord_2038307).sum := by decide
  have hdescent : baseEnd_2038307 < baseStart_2038307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038425 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2038425 : Nat := 118140960795 + 2038425 * 2 ^ 59
def prefixEnd_2038425 : Nat := 4983230072969 + 3 ^ 40 * 2038425 * 2
def baseEnd_2038425 : Nat := 465196356951685505116871

theorem tailTrace_2038425 : CollatzResearch.WordTrace tailWord_2038425 prefixEnd_2038425 465196356951685505116871 := by
  unfold tailWord_2038425
  simp only [CollatzResearch.WordTrace]
  refine ⟨74347467640141835118644729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49564978426761223412429819 74347467640141835118644729)
  ·
    refine ⟨55760600730106376338983547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74347467640141835118644729 55760600730106376338983547)
    ·
      refine ⟨83640901095159564508475321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55760600730106376338983547 83640901095159564508475321)
      ·
        refine ⟨62730675821369673381356491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83640901095159564508475321 62730675821369673381356491)
        ·
          refine ⟨94096013732054510072034737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62730675821369673381356491 94096013732054510072034737)
          ·
            refine ⟨70572010299040882554026053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94096013732054510072034737 70572010299040882554026053)
            ·
              refine ⟨13232251931070165478879885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70572010299040882554026053 13232251931070165478879885)
              ·
                refine ⟨4962094474151312054579957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13232251931070165478879885 4962094474151312054579957)
                ·
                  refine ⟨465196356951685505116871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4962094474151312054579957 465196356951685505116871)
                  ·
                    rfl

theorem cell21_2038425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2038425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038425 prefixEnd_2038425 := by exact prefixLift 2038425
  have htrace : WordTrace (prefixWord ++ tailWord_2038425) baseStart_2038425 baseEnd_2038425 := by
    simpa [prefixWord, tailWord_2038425, baseEnd_2038425] using wordTrace_append hprefix tailTrace_2038425
  have hstable : (prefixWord ++ tailWord_2038425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038425).length < 2 ^ (prefixWord ++ tailWord_2038425).sum := by decide
  have hdescent : baseEnd_2038425 < baseStart_2038425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038428 : List Nat := [2, 2, 3, 2, 2, 3, 1, 6]
def baseStart_2038428 : Nat := 118140960795 + 2038428 * 2 ^ 59
def prefixEnd_2038428 : Nat := 4983230072969 + 3 ^ 40 * 2038428 * 2
def baseEnd_2038428 : Nat := 155065680530852722188955

theorem tailTrace_2038428 : CollatzResearch.WordTrace tailWord_2038428 prefixEnd_2038428 155065680530852722188955 := by
  unfold tailWord_2038428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173788529565483315501969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49565051372753977754002625 37173788529565483315501969)
  ·
    refine ⟨27880341397174112486626477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37173788529565483315501969 27880341397174112486626477)
    ·
      refine ⟨10455128023940292182484929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27880341397174112486626477 10455128023940292182484929)
      ·
        refine ⟨7841346017955219136863697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10455128023940292182484929 7841346017955219136863697)
        ·
          refine ⟨5881009513466414352647773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7841346017955219136863697 5881009513466414352647773)
          ·
            refine ⟨2205378567549905382242915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5881009513466414352647773 2205378567549905382242915)
            ·
              refine ⟨3308067851324858073364373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205378567549905382242915 3308067851324858073364373)
              ·
                refine ⟨155065680530852722188955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3308067851324858073364373 155065680530852722188955)
                ·
                  rfl

theorem cell21_2038428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_2038428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038428 prefixEnd_2038428 := by exact prefixLift 2038428
  have htrace : WordTrace (prefixWord ++ tailWord_2038428) baseStart_2038428 baseEnd_2038428 := by
    simpa [prefixWord, tailWord_2038428, baseEnd_2038428] using wordTrace_append hprefix tailTrace_2038428
  have hstable : (prefixWord ++ tailWord_2038428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038428).length < 2 ^ (prefixWord ++ tailWord_2038428).sum := by decide
  have hdescent : baseEnd_2038428 < baseStart_2038428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038532 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_2038532 : Nat := 118140960795 + 2038532 * 2 ^ 59
def prefixEnd_2038532 : Nat := 4983230072969 + 3 ^ 40 * 2038532 * 2
def baseEnd_2038532 : Nat := 465220775809477096833319

theorem tailTrace_2038532 : CollatzResearch.WordTrace tailWord_2038532 prefixEnd_2038532 465220775809477096833319 := by
  unfold tailWord_2038532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37175685125377096196394925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49567580167169461595193233 37175685125377096196394925)
  ·
    refine ⟨13940881922016411073648097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37175685125377096196394925 13940881922016411073648097)
    ·
      refine ⟨10455661441512308305236073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13940881922016411073648097 10455661441512308305236073)
      ·
        refine ⟨7841746081134231228927055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10455661441512308305236073 7841746081134231228927055)
        ·
          refine ⟨11762619121701346843390583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841746081134231228927055 11762619121701346843390583)
          ·
            refine ⟨17643928682552020265085875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762619121701346843390583 17643928682552020265085875)
            ·
              refine ⟨26465893023828030397628813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643928682552020265085875 26465893023828030397628813)
              ·
                refine ⟨9924709883935511399110805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26465893023828030397628813 9924709883935511399110805)
                ·
                  refine ⟨465220775809477096833319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9924709883935511399110805 465220775809477096833319)
                  ·
                    rfl

theorem cell21_2038532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_2038532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038532 prefixEnd_2038532 := by exact prefixLift 2038532
  have htrace : WordTrace (prefixWord ++ tailWord_2038532) baseStart_2038532 baseEnd_2038532 := by
    simpa [prefixWord, tailWord_2038532, baseEnd_2038532] using wordTrace_append hprefix tailTrace_2038532
  have hstable : (prefixWord ++ tailWord_2038532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038532).length < 2 ^ (prefixWord ++ tailWord_2038532).sum := by decide
  have hdescent : baseEnd_2038532 < baseStart_2038532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038535 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 5]
def baseStart_2038535 : Nat := 118140960795 + 2038535 * 2 ^ 59
def prefixEnd_2038535 : Nat := 4983230072969 + 3 ^ 40 * 2038535 * 2
def baseEnd_2038535 : Nat := 465221460450349758283313

theorem tailTrace_2038535 : CollatzResearch.WordTrace tailWord_2038535 prefixEnd_2038535 465221460450349758283313 := by
  unfold tailWord_2038535
  simp only [CollatzResearch.WordTrace]
  refine ⟨74351479669743323905149059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49567653113162215936766039 74351479669743323905149059)
  ·
    refine ⟨111527219504614985857723589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74351479669743323905149059 111527219504614985857723589)
    ·
      refine ⟨20911353657115309848323173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111527219504614985857723589 20911353657115309848323173)
      ·
        refine ⟨3920878810709120596560595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20911353657115309848323173 3920878810709120596560595)
        ·
          refine ⟨5881318216063680894840893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920878810709120596560595 5881318216063680894840893)
          ·
            refine ⟨2205494331023880335565335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5881318216063680894840893 2205494331023880335565335)
            ·
              refine ⟨3308241496535820503348003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205494331023880335565335 3308241496535820503348003)
              ·
                refine ⟨4962362244803730755022005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308241496535820503348003 4962362244803730755022005)
                ·
                  refine ⟨465221460450349758283313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4962362244803730755022005 465221460450349758283313)
                  ·
                    rfl

theorem cell21_2038535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_2038535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038535 prefixEnd_2038535 := by exact prefixLift 2038535
  have htrace : WordTrace (prefixWord ++ tailWord_2038535) baseStart_2038535 baseEnd_2038535 := by
    simpa [prefixWord, tailWord_2038535, baseEnd_2038535] using wordTrace_append hprefix tailTrace_2038535
  have hstable : (prefixWord ++ tailWord_2038535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038535).length < 2 ^ (prefixWord ++ tailWord_2038535).sum := by decide
  have hdescent : baseEnd_2038535 < baseStart_2038535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038580 : List Nat := [2, 5, 1, 1, 4, 8]
def baseStart_2038580 : Nat := 118140960795 + 2038580 * 2 ^ 59
def prefixEnd_2038580 : Nat := 4983230072969 + 3 ^ 40 * 2038580 * 2
def baseEnd_2038580 : Nat := 17230804817164432593823

theorem tailTrace_2038580 : CollatzResearch.WordTrace tailWord_2038580 prefixEnd_2038580 17230804817164432593823 := by
  unfold tailWord_2038580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37176560477290148295268597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49568747303053531060358129 37176560477290148295268597)
  ·
    refine ⟨3485302544745951402681431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37176560477290148295268597 3485302544745951402681431)
    ·
      refine ⟨5227953817118927104022147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485302544745951402681431 5227953817118927104022147)
      ·
        refine ⟨7841930725678390656033221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227953817118927104022147 7841930725678390656033221)
        ·
          refine ⟨1470362011064698248006229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7841930725678390656033221 1470362011064698248006229)
          ·
            refine ⟨17230804817164432593823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1470362011064698248006229 17230804817164432593823)
            ·
              rfl

theorem cell21_2038580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 8].length) (baseStart_2038580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038580 prefixEnd_2038580 := by exact prefixLift 2038580
  have htrace : WordTrace (prefixWord ++ tailWord_2038580) baseStart_2038580 baseEnd_2038580 := by
    simpa [prefixWord, tailWord_2038580, baseEnd_2038580] using wordTrace_append hprefix tailTrace_2038580
  have hstable : (prefixWord ++ tailWord_2038580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038580).length < 2 ^ (prefixWord ++ tailWord_2038580).sum := by decide
  have hdescent : baseEnd_2038580 < baseStart_2038580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038608 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_2038608 : Nat := 118140960795 + 2038608 * 2 ^ 59
def prefixEnd_2038608 : Nat := 4983230072969 + 3 ^ 40 * 2038608 * 2
def baseEnd_2038608 : Nat := 465238120044917853566497

theorem tailTrace_2038608 : CollatzResearch.WordTrace tailWord_2038608 prefixEnd_2038608 465238120044917853566497 := by
  unfold tailWord_2038608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37177071099239428686278239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49569428132319238248370985 37177071099239428686278239)
  ·
    refine ⟨55765606648859143029417359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37177071099239428686278239 55765606648859143029417359)
    ·
      refine ⟨83648409973288714544126039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55765606648859143029417359 83648409973288714544126039)
      ·
        refine ⟨125472614959933071816189059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83648409973288714544126039 125472614959933071816189059)
        ·
          refine ⟨188208922439899607724283589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125472614959933071816189059 188208922439899607724283589)
          ·
            refine ⟨35289172957481176448303173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188208922439899607724283589 35289172957481176448303173)
            ·
              refine ⟨6616719929527720584056845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35289172957481176448303173 6616719929527720584056845)
              ·
                refine ⟨2481269973572895219021317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6616719929527720584056845 2481269973572895219021317)
                ·
                  refine ⟨465238120044917853566497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481269973572895219021317 465238120044917853566497)
                  ·
                    rfl

theorem cell21_2038608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_2038608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038608 prefixEnd_2038608 := by exact prefixLift 2038608
  have htrace : WordTrace (prefixWord ++ tailWord_2038608) baseStart_2038608 baseEnd_2038608 := by
    simpa [prefixWord, tailWord_2038608, baseEnd_2038608] using wordTrace_append hprefix tailTrace_2038608
  have hstable : (prefixWord ++ tailWord_2038608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038608).length < 2 ^ (prefixWord ++ tailWord_2038608).sum := by decide
  have hdescent : baseEnd_2038608 < baseStart_2038608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038653 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2038653 : Nat := 118140960795 + 2038653 * 2 ^ 59
def prefixEnd_2038653 : Nat := 4983230072969 + 3 ^ 40 * 2038653 * 2
def baseEnd_2038653 : Nat := 465248389658007775316405

theorem tailTrace_2038653 : CollatzResearch.WordTrace tailWord_2038653 prefixEnd_2038653 465248389658007775316405 := by
  unfold tailWord_2038653
  simp only [CollatzResearch.WordTrace]
  refine ⟨74355783483315830057944613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49570522322210553371963075 74355783483315830057944613)
  ·
    refine ⟨13941709403121718135864615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74355783483315830057944613 13941709403121718135864615)
    ·
      refine ⟨20912564104682577203796923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13941709403121718135864615 20912564104682577203796923)
      ·
        refine ⟨31368846157023865805695385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20912564104682577203796923 31368846157023865805695385)
        ·
          refine ⟨23526634617767899354271539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31368846157023865805695385 23526634617767899354271539)
          ·
            refine ⟨35289951926651849031407309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23526634617767899354271539 35289951926651849031407309)
            ·
              refine ⟨13233731972494443386777741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35289951926651849031407309 13233731972494443386777741)
              ·
                refine ⟨4962649489685416270041653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13233731972494443386777741 4962649489685416270041653)
                ·
                  refine ⟨465248389658007775316405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4962649489685416270041653 465248389658007775316405)
                  ·
                    rfl

theorem cell21_2038653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2038653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038653 prefixEnd_2038653 := by exact prefixLift 2038653
  have htrace : WordTrace (prefixWord ++ tailWord_2038653) baseStart_2038653 baseEnd_2038653 := by
    simpa [prefixWord, tailWord_2038653, baseEnd_2038653] using wordTrace_append hprefix tailTrace_2038653
  have hstable : (prefixWord ++ tailWord_2038653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038653).length < 2 ^ (prefixWord ++ tailWord_2038653).sum := by decide
  have hdescent : baseEnd_2038653 < baseStart_2038653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038687 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 3]
def baseStart_2038687 : Nat := 118140960795 + 2038687 * 2 ^ 59
def prefixEnd_2038687 : Nat := 4983230072969 + 3 ^ 40 * 2038687 * 2
def baseEnd_2038687 : Nat := 465256148921231271749669

theorem tailTrace_2038687 : CollatzResearch.WordTrace tailWord_2038687 prefixEnd_2038687 465256148921231271749669 := by
  unfold tailWord_2038687
  simp only [CollatzResearch.WordTrace]
  refine ⟨74357023565192653864682315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49571349043461769243121543 74357023565192653864682315)
  ·
    refine ⟨111535535347788980797023473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74357023565192653864682315 111535535347788980797023473)
    ·
      refine ⟨83651651510841735597767605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111535535347788980797023473 83651651510841735597767605)
      ·
        refine ⟨7842342329141412712290713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83651651510841735597767605 7842342329141412712290713)
        ·
          refine ⟨5881756746856059534218035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842342329141412712290713 5881756746856059534218035)
          ·
            refine ⟨8822635120284089301327053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881756746856059534218035 8822635120284089301327053)
            ·
              refine ⟨3308488170106533487997645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8822635120284089301327053 3308488170106533487997645)
              ·
                refine ⟨1240683063789950057999117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3308488170106533487997645 1240683063789950057999117)
                ·
                  refine ⟨465256148921231271749669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240683063789950057999117 465256148921231271749669)
                  ·
                    rfl

theorem cell21_2038687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 3].length) (baseStart_2038687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038687 prefixEnd_2038687 := by exact prefixLift 2038687
  have htrace : WordTrace (prefixWord ++ tailWord_2038687) baseStart_2038687 baseEnd_2038687 := by
    simpa [prefixWord, tailWord_2038687, baseEnd_2038687] using wordTrace_append hprefix tailTrace_2038687
  have hstable : (prefixWord ++ tailWord_2038687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038687).length < 2 ^ (prefixWord ++ tailWord_2038687).sum := by decide
  have hdescent : baseEnd_2038687 < baseStart_2038687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038710 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_2038710 : Nat := 118140960795 + 2038710 * 2 ^ 59
def prefixEnd_2038710 : Nat := 4983230072969 + 3 ^ 40 * 2038710 * 2
def baseEnd_2038710 : Nat := 465261397834588342866289

theorem tailTrace_2038710 : CollatzResearch.WordTrace tailWord_2038710 prefixEnd_2038710 465261397834588342866289 := by
  unfold tailWord_2038710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647366402756833049548099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49571908296072885861846389 4647366402756833049548099)
  ·
    refine ⟨6971049604135249574322149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4647366402756833049548099 6971049604135249574322149)
    ·
      refine ⟨1307071800775359295185403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6971049604135249574322149 1307071800775359295185403)
      ·
        refine ⟨1960607701163038942778105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307071800775359295185403 1960607701163038942778105)
        ·
          refine ⟨1470455775872279207083579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960607701163038942778105 1470455775872279207083579)
          ·
            refine ⟨2205683663808418810625369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470455775872279207083579 2205683663808418810625369)
            ·
              refine ⟨1654262747856314107969027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205683663808418810625369 1654262747856314107969027)
              ·
                refine ⟨2481394121784471161953541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654262747856314107969027 2481394121784471161953541)
                ·
                  refine ⟨465261397834588342866289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481394121784471161953541 465261397834588342866289)
                  ·
                    rfl

theorem cell21_2038710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_2038710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038710 prefixEnd_2038710 := by exact prefixLift 2038710
  have htrace : WordTrace (prefixWord ++ tailWord_2038710) baseStart_2038710 baseEnd_2038710 := by
    simpa [prefixWord, tailWord_2038710, baseEnd_2038710] using wordTrace_append hprefix tailTrace_2038710
  have hstable : (prefixWord ++ tailWord_2038710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038710).length < 2 ^ (prefixWord ++ tailWord_2038710).sum := by decide
  have hdescent : baseEnd_2038710 < baseStart_2038710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038743 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_2038743 : Nat := 118140960795 + 2038743 * 2 ^ 59
def prefixEnd_2038743 : Nat := 4983230072969 + 3 ^ 40 * 2038743 * 2
def baseEnd_2038743 : Nat := 465268928884187618816221

theorem tailTrace_2038743 : CollatzResearch.WordTrace tailWord_2038743 prefixEnd_2038743 465268928884187618816221 := by
  unfold tailWord_2038743
  simp only [CollatzResearch.WordTrace]
  refine ⟨74359066052989775428720883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49572710701993183619147255 74359066052989775428720883)
  ·
    refine ⟨111538599079484663143081325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74359066052989775428720883 111538599079484663143081325)
    ·
      refine ⟨41826974654806748678655497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111538599079484663143081325 41826974654806748678655497)
      ·
        refine ⟨31370230991105061508991623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41826974654806748678655497 31370230991105061508991623)
        ·
          refine ⟨47055346486657592263487435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31370230991105061508991623 47055346486657592263487435)
          ·
            refine ⟨70583019729986388395231153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47055346486657592263487435 70583019729986388395231153)
            ·
              refine ⟨52937264797489791296423365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70583019729986388395231153 52937264797489791296423365)
              ·
                refine ⟨9925737149529335868079381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52937264797489791296423365 9925737149529335868079381)
                ·
                  refine ⟨465268928884187618816221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9925737149529335868079381 465268928884187618816221)
                  ·
                    rfl

theorem cell21_2038743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_2038743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038743 prefixEnd_2038743 := by exact prefixLift 2038743
  have htrace : WordTrace (prefixWord ++ tailWord_2038743) baseStart_2038743 baseEnd_2038743 := by
    simpa [prefixWord, tailWord_2038743, baseEnd_2038743] using wordTrace_append hprefix tailTrace_2038743
  have hstable : (prefixWord ++ tailWord_2038743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038743).length < 2 ^ (prefixWord ++ tailWord_2038743).sum := by decide
  have hdescent : baseEnd_2038743 < baseStart_2038743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038760 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_2038760 : Nat := 118140960795 + 2038760 * 2 ^ 59
def prefixEnd_2038760 : Nat := 4983230072969 + 3 ^ 40 * 2038760 * 2
def baseEnd_2038760 : Nat := 465272808515799367032853

theorem tailTrace_2038760 : CollatzResearch.WordTrace tailWord_2038760 prefixEnd_2038760 465272808515799367032853 := by
  unfold tailWord_2038760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37179843046964093666044867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49573124062618791554726489 37179843046964093666044867)
  ·
    refine ⟨55769764570446140499067301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37179843046964093666044867 55769764570446140499067301)
    ·
      refine ⟨10456830856958651343575119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55769764570446140499067301 10456830856958651343575119)
      ·
        refine ⟨15685246285437977015362679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456830856958651343575119 15685246285437977015362679)
        ·
          refine ⟨23527869428156965523044019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15685246285437977015362679 23527869428156965523044019)
          ·
            refine ⟨35291804142235448284566029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23527869428156965523044019 35291804142235448284566029)
            ·
              refine ⟨13234426553338293106712261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35291804142235448284566029 13234426553338293106712261)
              ·
                refine ⟨2481454978750929957508549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13234426553338293106712261 2481454978750929957508549)
                ·
                  refine ⟨465272808515799367032853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481454978750929957508549 465272808515799367032853)
                  ·
                    rfl

theorem cell21_2038760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_2038760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038760 prefixEnd_2038760 := by exact prefixLift 2038760
  have htrace : WordTrace (prefixWord ++ tailWord_2038760) baseStart_2038760 baseEnd_2038760 := by
    simpa [prefixWord, tailWord_2038760, baseEnd_2038760] using wordTrace_append hprefix tailTrace_2038760
  have hstable : (prefixWord ++ tailWord_2038760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038760).length < 2 ^ (prefixWord ++ tailWord_2038760).sum := by decide
  have hdescent : baseEnd_2038760 < baseStart_2038760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038791 : List Nat := [1, 1, 4, 3, 1, 1, 5, 5]
def baseStart_2038791 : Nat := 118140960795 + 2038791 * 2 ^ 59
def prefixEnd_2038791 : Nat := 4983230072969 + 3 ^ 40 * 2038791 * 2
def baseEnd_2038791 : Nat := 155093294379383400672041

theorem tailTrace_2038791 : CollatzResearch.WordTrace tailWord_2038791 prefixEnd_2038791 155093294379383400672041 := by
  unfold tailWord_2038791
  simp only [CollatzResearch.WordTrace]
  refine ⟨74360816756815879626468227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49573877837877253084312151 74360816756815879626468227)
  ·
    refine ⟨111541225135223819439702341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74360816756815879626468227 111541225135223819439702341)
    ·
      refine ⟨20913979712854466144944189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111541225135223819439702341 20913979712854466144944189)
      ·
        refine ⟨7842742392320424804354071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20913979712854466144944189 7842742392320424804354071)
        ·
          refine ⟨11764113588480637206531107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842742392320424804354071 11764113588480637206531107)
          ·
            refine ⟨17646170382720955809796661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11764113588480637206531107 17646170382720955809796661)
            ·
              refine ⟨1654328473380089607168437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17646170382720955809796661 1654328473380089607168437)
              ·
                refine ⟨155093294379383400672041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1654328473380089607168437 155093294379383400672041)
                ·
                  rfl

theorem cell21_2038791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 5].length) (baseStart_2038791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038791 prefixEnd_2038791 := by exact prefixLift 2038791
  have htrace : WordTrace (prefixWord ++ tailWord_2038791) baseStart_2038791 baseEnd_2038791 := by
    simpa [prefixWord, tailWord_2038791, baseEnd_2038791] using wordTrace_append hprefix tailTrace_2038791
  have hstable : (prefixWord ++ tailWord_2038791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038791).length < 2 ^ (prefixWord ++ tailWord_2038791).sum := by decide
  have hdescent : baseEnd_2038791 < baseStart_2038791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038864 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_2038864 : Nat := 118140960795 + 2038864 * 2 ^ 59
def prefixEnd_2038864 : Nat := 4983230072969 + 3 ^ 40 * 2038864 * 2
def baseEnd_2038864 : Nat := 465296542732718297299307

theorem tailTrace_2038864 : CollatzResearch.WordTrace tailWord_2038864 prefixEnd_2038864 465296542732718297299307 := by
  unfold tailWord_2038864
  simp only [CollatzResearch.WordTrace]
  refine ⟨37181739642775706546937823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49575652857034275395917097 37181739642775706546937823)
  ·
    refine ⟨55772609464163559820406735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37181739642775706546937823 55772609464163559820406735)
    ·
      refine ⟨83658914196245339730610103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55772609464163559820406735 83658914196245339730610103)
      ·
        refine ⟨125488371294368009595915155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83658914196245339730610103 125488371294368009595915155)
        ·
          refine ⟨188232556941552014393872733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125488371294368009595915155 188232556941552014393872733)
          ·
            refine ⟨70587208853082005397702275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188232556941552014393872733 70587208853082005397702275)
            ·
              refine ⟨105880813279623008096553413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70587208853082005397702275 105880813279623008096553413)
              ·
                refine ⟨19852652489929314018103765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105880813279623008096553413 19852652489929314018103765)
                ·
                  refine ⟨465296542732718297299307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19852652489929314018103765 465296542732718297299307)
                  ·
                    rfl

theorem cell21_2038864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_2038864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038864 prefixEnd_2038864 := by exact prefixLift 2038864
  have htrace : WordTrace (prefixWord ++ tailWord_2038864) baseStart_2038864 baseEnd_2038864 := by
    simpa [prefixWord, tailWord_2038864, baseEnd_2038864] using wordTrace_append hprefix tailTrace_2038864
  have hstable : (prefixWord ++ tailWord_2038864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038864).length < 2 ^ (prefixWord ++ tailWord_2038864).sum := by decide
  have hdescent : baseEnd_2038864 < baseStart_2038864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038881 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_2038881 : Nat := 118140960795 + 2038881 * 2 ^ 59
def prefixEnd_2038881 : Nat := 4983230072969 + 3 ^ 40 * 2038881 * 2
def baseEnd_2038881 : Nat := 465300422364330045515939

theorem tailTrace_2038881 : CollatzResearch.WordTrace tailWord_2038881 prefixEnd_2038881 465300422364330045515939 := by
  unfold tailWord_2038881
  simp only [CollatzResearch.WordTrace]
  refine ⟨74364099326489824997244497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49576066217659883331496331 74364099326489824997244497)
  ·
    refine ⟨55773074494867368747933373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74364099326489824997244497 55773074494867368747933373)
    ·
      refine ⟨20914902935575263280475015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55773074494867368747933373 20914902935575263280475015)
      ·
        refine ⟨31372354403362894920712523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20914902935575263280475015 31372354403362894920712523)
        ·
          refine ⟨47058531605044342381068785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31372354403362894920712523 47058531605044342381068785)
          ·
            refine ⟨35293898703783256785801589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47058531605044342381068785 35293898703783256785801589)
            ·
              refine ⟨3308803003479680323668899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35293898703783256785801589 3308803003479680323668899)
              ·
                refine ⟨4963204505219520485503349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308803003479680323668899 4963204505219520485503349)
                ·
                  refine ⟨465300422364330045515939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4963204505219520485503349 465300422364330045515939)
                  ·
                    rfl

theorem cell21_2038881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_2038881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038881 prefixEnd_2038881 := by exact prefixLift 2038881
  have htrace : WordTrace (prefixWord ++ tailWord_2038881) baseStart_2038881 baseEnd_2038881 := by
    simpa [prefixWord, tailWord_2038881, baseEnd_2038881] using wordTrace_append hprefix tailTrace_2038881
  have hstable : (prefixWord ++ tailWord_2038881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038881).length < 2 ^ (prefixWord ++ tailWord_2038881).sum := by decide
  have hdescent : baseEnd_2038881 < baseStart_2038881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038926 : List Nat := [4, 1, 1, 3, 2, 10]
def baseStart_2038926 : Nat := 118140960795 + 2038926 * 2 ^ 59
def prefixEnd_2038926 : Nat := 4983230072969 + 3 ^ 40 * 2038926 * 2
def baseEnd_2038926 : Nat := 17233729332497035824661

theorem tailTrace_2038926 : CollatzResearch.WordTrace tailWord_2038926 prefixEnd_2038926 17233729332497035824661 := by
  unfold tailWord_2038926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295717576415849710329079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49577160407551198455088421 9295717576415849710329079)
  ·
    refine ⟨13943576364623774565493619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9295717576415849710329079 13943576364623774565493619)
    ·
      refine ⟨20915364546935661848240429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13943576364623774565493619 20915364546935661848240429)
      ·
        refine ⟨7843261705100873193090161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20915364546935661848240429 7843261705100873193090161)
        ·
          refine ⟨5882446278825654894817621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7843261705100873193090161 5882446278825654894817621)
          ·
            refine ⟨17233729332497035824661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5882446278825654894817621 17233729332497035824661)
            ·
              rfl

theorem cell21_2038926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 10].length) (baseStart_2038926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2038926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2038926 prefixEnd_2038926 := by exact prefixLift 2038926
  have htrace : WordTrace (prefixWord ++ tailWord_2038926) baseStart_2038926 baseEnd_2038926 := by
    simpa [prefixWord, tailWord_2038926, baseEnd_2038926] using wordTrace_append hprefix tailTrace_2038926
  have hstable : (prefixWord ++ tailWord_2038926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038926).length < 2 ^ (prefixWord ++ tailWord_2038926).sum := by decide
  have hdescent : baseEnd_2038926 < baseStart_2038926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039019 : List Nat := [1, 1, 1, 1, 2, 8, 2, 5]
def baseStart_2039019 : Nat := 118140960795 + 2039019 * 2 ^ 59
def prefixEnd_2039019 : Nat := 4983230072969 + 3 ^ 40 * 2039019 * 2
def baseEnd_2039019 : Nat := 155110638614824157405219

theorem tailTrace_2039019 : CollatzResearch.WordTrace tailWord_2039019 prefixEnd_2039019 155110638614824157405219 := by
  unfold tailWord_2039019
  simp only [CollatzResearch.WordTrace]
  refine ⟨74369132599989874565768111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49579421733326583043845407 74369132599989874565768111)
  ·
    refine ⟨111553698899984811848652167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74369132599989874565768111 111553698899984811848652167)
    ·
      refine ⟨167330548349977217772978251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111553698899984811848652167 167330548349977217772978251)
      ·
        refine ⟨250995822524965826659467377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167330548349977217772978251 250995822524965826659467377)
        ·
          refine ⟨188246866893724369994600533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250995822524965826659467377 188246866893724369994600533)
          ·
            refine ⟨2206017971410832460874225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 188246866893724369994600533 2206017971410832460874225)
            ·
              refine ⟨1654513478558124345655669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206017971410832460874225 1654513478558124345655669)
              ·
                refine ⟨155110638614824157405219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1654513478558124345655669 155110638614824157405219)
                ·
                  rfl

theorem cell21_2039019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 5].length) (baseStart_2039019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039019 prefixEnd_2039019 := by exact prefixLift 2039019
  have htrace : WordTrace (prefixWord ++ tailWord_2039019) baseStart_2039019 baseEnd_2039019 := by
    simpa [prefixWord, tailWord_2039019, baseEnd_2039019] using wordTrace_append hprefix tailTrace_2039019
  have hstable : (prefixWord ++ tailWord_2039019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039019).length < 2 ^ (prefixWord ++ tailWord_2039019).sum := by decide
  have hdescent : baseEnd_2039019 < baseStart_2039019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039064 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_2039064 : Nat := 118140960795 + 2039064 * 2 ^ 59
def prefixEnd_2039064 : Nat := 4983230072969 + 3 ^ 40 * 2039064 * 2
def baseEnd_2039064 : Nat := 465342185457562393965565

theorem tailTrace_2039064 : CollatzResearch.WordTrace tailWord_2039064 prefixEnd_2039064 465342185457562393965565 := by
  unfold tailWord_2039064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37185386942413423625578123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49580515923217898167437497 37185386942413423625578123)
  ·
    refine ⟨55778080413620135438367185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37185386942413423625578123 55778080413620135438367185)
    ·
      refine ⟨41833560310215101578775389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55778080413620135438367185 41833560310215101578775389)
      ·
        refine ⟨15687585116330663092040771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41833560310215101578775389 15687585116330663092040771)
        ·
          refine ⟨23531377674495994638061157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687585116330663092040771 23531377674495994638061157)
          ·
            refine ⟨4412133313967998994636467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23531377674495994638061157 4412133313967998994636467)
            ·
              refine ⟨6618199970951998491954701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412133313967998994636467 6618199970951998491954701)
              ·
                refine ⟨2481824989106999434483013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6618199970951998491954701 2481824989106999434483013)
                ·
                  refine ⟨465342185457562393965565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481824989106999434483013 465342185457562393965565)
                  ·
                    rfl

theorem cell21_2039064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_2039064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039064 prefixEnd_2039064 := by exact prefixLift 2039064
  have htrace : WordTrace (prefixWord ++ tailWord_2039064) baseStart_2039064 baseEnd_2039064 := by
    simpa [prefixWord, tailWord_2039064, baseEnd_2039064] using wordTrace_append hprefix tailTrace_2039064
  have hstable : (prefixWord ++ tailWord_2039064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039064).length < 2 ^ (prefixWord ++ tailWord_2039064).sum := by decide
  have hdescent : baseEnd_2039064 < baseStart_2039064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039101 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 3]
def baseStart_2039101 : Nat := 118140960795 + 2039101 * 2 ^ 59
def prefixEnd_2039101 : Nat := 4983230072969 + 3 ^ 40 * 2039101 * 2
def baseEnd_2039101 : Nat := 465350629361658551848823

theorem tailTrace_2039101 : CollatzResearch.WordTrace tailWord_2039101 prefixEnd_2039101 465350629361658551848823 := by
  unfold tailWord_2039101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372123385692802570253157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49581415590461868380168771 74372123385692802570253157)
  ·
    refine ⟨13944773134817400481922467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74372123385692802570253157 13944773134817400481922467)
    ·
      refine ⟨20917159702226100722883701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13944773134817400481922467 20917159702226100722883701)
      ·
        refine ⟨1960983722083696942770347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20917159702226100722883701 1960983722083696942770347)
        ·
          refine ⟨2941475583125545414155521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960983722083696942770347 2941475583125545414155521)
          ·
            refine ⟨2206106687344159060616641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2941475583125545414155521 2206106687344159060616641)
            ·
              refine ⟨1654580015508119295462481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206106687344159060616641 1654580015508119295462481)
              ·
                refine ⟨1240935011631089471596861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654580015508119295462481 1240935011631089471596861)
                ·
                  refine ⟨465350629361658551848823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240935011631089471596861 465350629361658551848823)
                  ·
                    rfl

theorem cell21_2039101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_2039101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039101 prefixEnd_2039101 := by exact prefixLift 2039101
  have htrace : WordTrace (prefixWord ++ tailWord_2039101) baseStart_2039101 baseEnd_2039101 := by
    simpa [prefixWord, tailWord_2039101, baseEnd_2039101] using wordTrace_append hprefix tailTrace_2039101
  have hstable : (prefixWord ++ tailWord_2039101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039101).length < 2 ^ (prefixWord ++ tailWord_2039101).sum := by decide
  have hdescent : baseEnd_2039101 < baseStart_2039101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039123 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_2039123 : Nat := 118140960795 + 2039123 * 2 ^ 59
def prefixEnd_2039123 : Nat := 4983230072969 + 3 ^ 40 * 2039123 * 2
def baseEnd_2039123 : Nat := 465355650061391402482111

theorem tailTrace_2039123 : CollatzResearch.WordTrace tailWord_2039123 prefixEnd_2039123 465355650061391402482111 := by
  unfold tailWord_2039123
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372925791613100327554023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49581950527742066885036015 74372925791613100327554023)
  ·
    refine ⟨111559388687419650491331035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74372925791613100327554023 111559388687419650491331035)
    ·
      refine ⟨167339083031129475736996553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111559388687419650491331035 167339083031129475736996553)
      ·
        refine ⟨125504312273347106802747415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167339083031129475736996553 125504312273347106802747415)
        ·
          refine ⟨188256468410020660204121123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125504312273347106802747415 188256468410020660204121123)
          ·
            refine ⟨282384702615030990306181685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188256468410020660204121123 282384702615030990306181685)
            ·
              refine ⟨26473565870159155341204533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282384702615030990306181685 26473565870159155341204533)
              ·
                refine ⟨2481896800327420813237925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26473565870159155341204533 2481896800327420813237925)
                ·
                  refine ⟨465355650061391402482111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2481896800327420813237925 465355650061391402482111)
                  ·
                    rfl

theorem cell21_2039123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_2039123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039123 prefixEnd_2039123 := by exact prefixLift 2039123
  have htrace : WordTrace (prefixWord ++ tailWord_2039123) baseStart_2039123 baseEnd_2039123 := by
    simpa [prefixWord, tailWord_2039123, baseEnd_2039123] using wordTrace_append hprefix tailTrace_2039123
  have hstable : (prefixWord ++ tailWord_2039123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039123).length < 2 ^ (prefixWord ++ tailWord_2039123).sum := by decide
  have hdescent : baseEnd_2039123 < baseStart_2039123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039137 : List Nat := [1, 2, 3, 1, 1, 1, 1, 11]
def baseStart_2039137 : Nat := 118140960795 + 2039137 * 2 ^ 59
def prefixEnd_2039137 : Nat := 4983230072969 + 3 ^ 40 * 2039137 * 2
def baseEnd_2039137 : Nat := 155119615017376829749583

theorem tailTrace_2039137 : CollatzResearch.WordTrace tailWord_2039137 prefixEnd_2039137 155119615017376829749583 := by
  unfold tailWord_2039137
  simp only [CollatzResearch.WordTrace]
  refine ⟨74373436413562380718563665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49582290942374920479042443 74373436413562380718563665)
  ·
    refine ⟨55780077310171785538922749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74373436413562380718563665 55780077310171785538922749)
    ·
      refine ⟨20917528991314419577096031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55780077310171785538922749 20917528991314419577096031)
      ·
        refine ⟨31376293486971629365644047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20917528991314419577096031 31376293486971629365644047)
        ·
          refine ⟨47064440230457444048466071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31376293486971629365644047 47064440230457444048466071)
          ·
            refine ⟨70596660345686166072699107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47064440230457444048466071 70596660345686166072699107)
            ·
              refine ⟨105894990518529249109048661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70596660345686166072699107 105894990518529249109048661)
              ·
                refine ⟨155119615017376829749583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105894990518529249109048661 155119615017376829749583)
                ·
                  rfl

theorem cell21_2039137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_2039137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039137 prefixEnd_2039137 := by exact prefixLift 2039137
  have htrace : WordTrace (prefixWord ++ tailWord_2039137) baseStart_2039137 baseEnd_2039137 := by
    simpa [prefixWord, tailWord_2039137, baseEnd_2039137] using wordTrace_append hprefix tailTrace_2039137
  have hstable : (prefixWord ++ tailWord_2039137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039137).length < 2 ^ (prefixWord ++ tailWord_2039137).sum := by decide
  have hdescent : baseEnd_2039137 < baseStart_2039137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039143 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 3]
def baseStart_2039143 : Nat := 118140960795 + 2039143 * 2 ^ 59
def prefixEnd_2039143 : Nat := 4983230072969 + 3 ^ 40 * 2039143 * 2
def baseEnd_2039143 : Nat := 465360214333875812148737

theorem tailTrace_2039143 : CollatzResearch.WordTrace tailWord_2039143 prefixEnd_2039143 465360214333875812148737 := by
  unfold tailWord_2039143
  simp only [CollatzResearch.WordTrace]
  refine ⟨74373655251540643743282083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49582436834360429162188055 74373655251540643743282083)
  ·
    refine ⟨111560482877310965614923125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74373655251540643743282083 111560482877310965614923125)
    ·
      refine ⟨10458795269747903026399043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111560482877310965614923125 10458795269747903026399043)
      ·
        refine ⟨15688192904621854539598565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10458795269747903026399043 15688192904621854539598565)
        ·
          refine ⟨2941536169616597726174731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15688192904621854539598565 2941536169616597726174731)
          ·
            refine ⟨4412304254424896589262097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941536169616597726174731 4412304254424896589262097)
            ·
              refine ⟨3309228190818672441946573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4412304254424896589262097 3309228190818672441946573)
              ·
                refine ⟨1240960571557002165729965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309228190818672441946573 1240960571557002165729965)
                ·
                  refine ⟨465360214333875812148737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240960571557002165729965 465360214333875812148737)
                  ·
                    rfl

theorem cell21_2039143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 3].length) (baseStart_2039143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039143 prefixEnd_2039143 := by exact prefixLift 2039143
  have htrace : WordTrace (prefixWord ++ tailWord_2039143) baseStart_2039143 baseEnd_2039143 := by
    simpa [prefixWord, tailWord_2039143, baseEnd_2039143] using wordTrace_append hprefix tailTrace_2039143
  have hstable : (prefixWord ++ tailWord_2039143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039143).length < 2 ^ (prefixWord ++ tailWord_2039143).sum := by decide
  have hdescent : baseEnd_2039143 < baseStart_2039143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039188 : List Nat := [2, 4, 2, 1, 2, 3, 2, 5]
def baseStart_2039188 : Nat := 118140960795 + 2039188 * 2 ^ 59
def prefixEnd_2039188 : Nat := 4983230072969 + 3 ^ 40 * 2039188 * 2
def baseEnd_2039188 : Nat := 155123494648988577966215

theorem tailTrace_2039188 : CollatzResearch.WordTrace tailWord_2039188 prefixEnd_2039188 155123494648988577966215 := by
  unfold tailWord_2039188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37187648268188808214335109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49583531024251744285780145 37187648268188808214335109)
  ·
    refine ⟨6972684050285401540187833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37187648268188808214335109 6972684050285401540187833)
    ·
      refine ⟨5229513037714051155140875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6972684050285401540187833 5229513037714051155140875)
      ·
        refine ⟨7844269556571076732711313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229513037714051155140875 7844269556571076732711313)
        ·
          refine ⟨5883202167428307549533485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7844269556571076732711313 5883202167428307549533485)
          ·
            refine ⟨2206200812785615331075057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5883202167428307549533485 2206200812785615331075057)
            ·
              refine ⟨1654650609589211498306293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206200812785615331075057 1654650609589211498306293)
              ·
                refine ⟨155123494648988577966215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1654650609589211498306293 155123494648988577966215)
                ·
                  rfl

theorem cell21_2039188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_2039188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039188 prefixEnd_2039188 := by exact prefixLift 2039188
  have htrace : WordTrace (prefixWord ++ tailWord_2039188) baseStart_2039188 baseEnd_2039188 := by
    simpa [prefixWord, tailWord_2039188, baseEnd_2039188] using wordTrace_append hprefix tailTrace_2039188
  have hstable : (prefixWord ++ tailWord_2039188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039188).length < 2 ^ (prefixWord ++ tailWord_2039188).sum := by decide
  have hdescent : baseEnd_2039188 < baseStart_2039188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039199 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_2039199 : Nat := 118140960795 + 2039199 * 2 ^ 59
def prefixEnd_2039199 : Nat := 4983230072969 + 3 ^ 40 * 2039199 * 2
def baseEnd_2039199 : Nat := 465372994296832159215289

theorem tailTrace_2039199 : CollatzResearch.WordTrace tailWord_2039199 prefixEnd_2039199 465372994296832159215289 := by
  unfold tailWord_2039199
  simp only [CollatzResearch.WordTrace]
  refine ⟨74375697739337765307320651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49583798492891843538213767 74375697739337765307320651)
  ·
    refine ⟨111563546609006647960980977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74375697739337765307320651 111563546609006647960980977)
    ·
      refine ⟨83672659956754985970735733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111563546609006647960980977 83672659956754985970735733)
      ·
        refine ⟨7844311870945779934756475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83672659956754985970735733 7844311870945779934756475)
        ·
          refine ⟨11766467806418669902134713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844311870945779934756475 11766467806418669902134713)
          ·
            refine ⟨8824850854814002426601035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11766467806418669902134713 8824850854814002426601035)
            ·
              refine ⟨13237276282221003639901553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824850854814002426601035 13237276282221003639901553)
              ·
                refine ⟨9927957211665752729926165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13237276282221003639901553 9927957211665752729926165)
                ·
                  refine ⟨465372994296832159215289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9927957211665752729926165 465372994296832159215289)
                  ·
                    rfl

theorem cell21_2039199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_2039199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039199 prefixEnd_2039199 := by exact prefixLift 2039199
  have htrace : WordTrace (prefixWord ++ tailWord_2039199) baseStart_2039199 baseEnd_2039199 := by
    simpa [prefixWord, tailWord_2039199, baseEnd_2039199] using wordTrace_append hprefix tailTrace_2039199
  have hstable : (prefixWord ++ tailWord_2039199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039199).length < 2 ^ (prefixWord ++ tailWord_2039199).sum := by decide
  have hdescent : baseEnd_2039199 < baseStart_2039199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039278 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_2039278 : Nat := 118140960795 + 2039278 * 2 ^ 59
def prefixEnd_2039278 : Nat := 4983230072969 + 3 ^ 40 * 2039278 * 2
def baseEnd_2039278 : Nat := 465391023173145577398461

theorem tailTrace_2039278 : CollatzResearch.WordTrace tailWord_2039278 prefixEnd_2039278 465391023173145577398461 := by
  unfold tailWord_2039278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297322388256445224930811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49585719404034374532964325 9297322388256445224930811)
  ·
    refine ⟨13945983582384667837396217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9297322388256445224930811 13945983582384667837396217)
    ·
      refine ⟨10459487686788500878047163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13945983582384667837396217 10459487686788500878047163)
      ·
        refine ⟨15689231530182751317070745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10459487686788500878047163 15689231530182751317070745)
        ·
          refine ⟨11766923647637063487803059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15689231530182751317070745 11766923647637063487803059)
          ·
            refine ⟨17650385471455595231704589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766923647637063487803059 17650385471455595231704589)
            ·
              refine ⟨6618894551795848211889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17650385471455595231704589 6618894551795848211889221)
              ·
                refine ⟨1241042728461721539729229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6618894551795848211889221 1241042728461721539729229)
                ·
                  refine ⟨465391023173145577398461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241042728461721539729229 465391023173145577398461)
                  ·
                    rfl

theorem cell21_2039278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_2039278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039278 prefixEnd_2039278 := by exact prefixLift 2039278
  have htrace : WordTrace (prefixWord ++ tailWord_2039278) baseStart_2039278 baseEnd_2039278 := by
    simpa [prefixWord, tailWord_2039278, baseEnd_2039278] using wordTrace_append hprefix tailTrace_2039278
  have hstable : (prefixWord ++ tailWord_2039278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039278).length < 2 ^ (prefixWord ++ tailWord_2039278).sum := by decide
  have hdescent : baseEnd_2039278 < baseStart_2039278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039365 : List Nat := [1, 3, 1, 1, 1, 4, 3, 7]
def baseStart_2039365 : Nat := 118140960795 + 2039365 * 2 ^ 59
def prefixEnd_2039365 : Nat := 4983230072969 + 3 ^ 40 * 2039365 * 2
def baseEnd_2039365 : Nat := 155136959252817586482761

theorem tailTrace_2039365 : CollatzResearch.WordTrace tailWord_2039365 prefixEnd_2039365 155136959252817586482761 := by
  unfold tailWord_2039365
  simp only [CollatzResearch.WordTrace]
  refine ⟨74381752256736375657863549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49587834837824250438575699 74381752256736375657863549)
  ·
    refine ⟨27893157096276140871698831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74381752256736375657863549 27893157096276140871698831)
    ·
      refine ⟨41839735644414211307548247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27893157096276140871698831 41839735644414211307548247)
      ·
        refine ⟨62759603466621316961322371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41839735644414211307548247 62759603466621316961322371)
        ·
          refine ⟨94139405199931975441983557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62759603466621316961322371 94139405199931975441983557)
          ·
            refine ⟨17651138474987245395371917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94139405199931975441983557 17651138474987245395371917)
            ·
              refine ⟨6619176928120217023264469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17651138474987245395371917 6619176928120217023264469)
              ·
                refine ⟨155136959252817586482761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6619176928120217023264469 155136959252817586482761)
                ·
                  rfl

theorem cell21_2039365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_2039365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039365 prefixEnd_2039365 := by exact prefixLift 2039365
  have htrace : WordTrace (prefixWord ++ tailWord_2039365) baseStart_2039365 baseEnd_2039365 := by
    simpa [prefixWord, tailWord_2039365, baseEnd_2039365] using wordTrace_append hprefix tailTrace_2039365
  have hstable : (prefixWord ++ tailWord_2039365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039365).length < 2 ^ (prefixWord ++ tailWord_2039365).sum := by decide
  have hdescent : baseEnd_2039365 < baseStart_2039365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039447 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 3]
def baseStart_2039447 : Nat := 118140960795 + 2039447 * 2 ^ 59
def prefixEnd_2039447 : Nat := 4983230072969 + 3 ^ 40 * 2039447 * 2
def baseEnd_2039447 : Nat := 465429591275638839081449

theorem tailTrace_2039447 : CollatzResearch.WordTrace tailWord_2039447 prefixEnd_2039447 465429591275638839081449 := by
  unfold tailWord_2039447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74384743042439303662348595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49589828694959535774899063 74384743042439303662348595)
  ·
    refine ⟨111577114563658955493522893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74384743042439303662348595 111577114563658955493522893)
    ·
      refine ⟨41841417961372108310071085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111577114563658955493522893 41841417961372108310071085)
      ·
        refine ⟨15690531735514540616276657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41841417961372108310071085 15690531735514540616276657)
        ·
          refine ⟨11767898801635905462207493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15690531735514540616276657 11767898801635905462207493)
          ·
            refine ⟨2206481025306732274163905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11767898801635905462207493 2206481025306732274163905)
            ·
              refine ⟨1654860768980049205622929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206481025306732274163905 1654860768980049205622929)
              ·
                refine ⟨1241145576735036904217197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654860768980049205622929 1241145576735036904217197)
                ·
                  refine ⟨465429591275638839081449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241145576735036904217197 465429591275638839081449)
                  ·
                    rfl

theorem cell21_2039447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3].length) (baseStart_2039447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039447 prefixEnd_2039447 := by exact prefixLift 2039447
  have htrace : WordTrace (prefixWord ++ tailWord_2039447) baseStart_2039447 baseEnd_2039447 := by
    simpa [prefixWord, tailWord_2039447, baseEnd_2039447] using wordTrace_append hprefix tailTrace_2039447
  have hstable : (prefixWord ++ tailWord_2039447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039447).length < 2 ^ (prefixWord ++ tailWord_2039447).sum := by decide
  have hdescent : baseEnd_2039447 < baseStart_2039447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039506 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_2039506 : Nat := 118140960795 + 2039506 * 2 ^ 59
def prefixEnd_2039506 : Nat := 4983230072969 + 3 ^ 40 * 2039506 * 2
def baseEnd_2039506 : Nat := 465443055879467847597995

theorem tailTrace_2039506 : CollatzResearch.WordTrace tailWord_2039506 prefixEnd_2039506 465443055879467847597995 := by
  unfold tailWord_2039506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596723737306389184686593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49591263299483704492497581 18596723737306389184686593)
  ·
    refine ⟨13947542802979791888514945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18596723737306389184686593 13947542802979791888514945)
    ·
      refine ⟨10460657102234843916386209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13947542802979791888514945 10460657102234843916386209)
      ·
        refine ⟨7845492826676132937289657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10460657102234843916386209 7845492826676132937289657)
        ·
          refine ⟨5884119620007099702967243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845492826676132937289657 5884119620007099702967243)
          ·
            refine ⟨8826179430010649554450865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884119620007099702967243 8826179430010649554450865)
            ·
              refine ⟨6619634572507987165838149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8826179430010649554450865 6619634572507987165838149)
              ·
                refine ⟨1241181482345247593594653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6619634572507987165838149 1241181482345247593594653)
                ·
                  refine ⟨465443055879467847597995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241181482345247593594653 465443055879467847597995)
                  ·
                    rfl

theorem cell21_2039506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_2039506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039506 prefixEnd_2039506 := by exact prefixLift 2039506
  have htrace : WordTrace (prefixWord ++ tailWord_2039506) baseStart_2039506 baseEnd_2039506 := by
    simpa [prefixWord, tailWord_2039506, baseEnd_2039506] using wordTrace_append hprefix tailTrace_2039506
  have hstable : (prefixWord ++ tailWord_2039506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039506).length < 2 ^ (prefixWord ++ tailWord_2039506).sum := by decide
  have hdescent : baseEnd_2039506 < baseStart_2039506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039540 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2039540 : Nat := 118140960795 + 2039540 * 2 ^ 59
def prefixEnd_2039540 : Nat := 4983230072969 + 3 ^ 40 * 2039540 * 2
def baseEnd_2039540 : Nat := 465450815142691344031259

theorem tailTrace_2039540 : CollatzResearch.WordTrace tailWord_2039540 prefixEnd_2039540 465450815142691344031259 := by
  unfold tailWord_2039540
  simp only [CollatzResearch.WordTrace]
  refine ⟨37194067515551190272742037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49592090020734920363656049 37194067515551190272742037)
  ·
    refine ⟨1743471914791462044034783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37194067515551190272742037 1743471914791462044034783)
    ·
      refine ⟨2615207872187193066052175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743471914791462044034783 2615207872187193066052175)
      ·
        refine ⟨3922811808280789599078263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615207872187193066052175 3922811808280789599078263)
        ·
          refine ⟨5884217712421184398617395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922811808280789599078263 5884217712421184398617395)
          ·
            refine ⟨8826326568631776597926093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884217712421184398617395 8826326568631776597926093)
            ·
              refine ⟨3309872463236916224222285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8826326568631776597926093 3309872463236916224222285)
              ·
                refine ⟨1241202173713843584083357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309872463236916224222285 1241202173713843584083357)
                ·
                  refine ⟨465450815142691344031259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241202173713843584083357 465450815142691344031259)
                  ·
                    rfl

theorem cell21_2039540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2039540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039540 prefixEnd_2039540 := by exact prefixLift 2039540
  have htrace : WordTrace (prefixWord ++ tailWord_2039540) baseStart_2039540 baseEnd_2039540 := by
    simpa [prefixWord, tailWord_2039540, baseEnd_2039540] using wordTrace_append hprefix tailTrace_2039540
  have hstable : (prefixWord ++ tailWord_2039540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039540).length < 2 ^ (prefixWord ++ tailWord_2039540).sum := by decide
  have hdescent : baseEnd_2039540 < baseStart_2039540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039607 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_2039607 : Nat := 118140960795 + 2039607 * 2 ^ 59
def prefixEnd_2039607 : Nat := 4983230072969 + 3 ^ 40 * 2039607 * 2
def baseEnd_2039607 : Nat := 465466105455514116414455

theorem tailTrace_2039607 : CollatzResearch.WordTrace tailWord_2039607 prefixEnd_2039607 465466105455514116414455 := by
  unfold tailWord_2039607
  simp only [CollatzResearch.WordTrace]
  refine ⟨74390578721859650988173075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49593719147906433992115383 74390578721859650988173075)
  ·
    refine ⟨111585868082789476482259613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74390578721859650988173075 111585868082789476482259613)
    ·
      refine ⟨41844700531046053680847355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111585868082789476482259613 41844700531046053680847355)
      ·
        refine ⟨62767050796569080521271033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41844700531046053680847355 62767050796569080521271033)
        ·
          refine ⟨47075288097426810390953275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62767050796569080521271033 47075288097426810390953275)
          ·
            refine ⟨70612932146140215586429913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47075288097426810390953275 70612932146140215586429913)
            ·
              refine ⟨52959699109605161689822435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70612932146140215586429913 52959699109605161689822435)
              ·
                refine ⟨79439548664407742534733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52959699109605161689822435 79439548664407742534733653)
                ·
                  refine ⟨465466105455514116414455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79439548664407742534733653 465466105455514116414455)
                  ·
                    rfl

theorem cell21_2039607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_2039607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039607 prefixEnd_2039607 := by exact prefixLift 2039607
  have htrace : WordTrace (prefixWord ++ tailWord_2039607) baseStart_2039607 baseEnd_2039607 := by
    simpa [prefixWord, tailWord_2039607, baseEnd_2039607] using wordTrace_append hprefix tailTrace_2039607
  have hstable : (prefixWord ++ tailWord_2039607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039607).length < 2 ^ (prefixWord ++ tailWord_2039607).sum := by decide
  have hdescent : baseEnd_2039607 < baseStart_2039607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039669 : List Nat := [1, 3, 4, 1, 1, 1, 10]
def baseStart_2039669 : Nat := 118140960795 + 2039669 * 2 ^ 59
def prefixEnd_2039669 : Nat := 4983230072969 + 3 ^ 40 * 2039669 * 2
def baseEnd_2039669 : Nat := 51720028300023976264555

theorem tailTrace_2039669 : CollatzResearch.WordTrace tailWord_2039669 prefixEnd_2039669 51720028300023976264555 := by
  unfold tailWord_2039669
  simp only [CollatzResearch.WordTrace]
  refine ⟨74392840047635035576930061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49595226698423357051286707 74392840047635035576930061)
  ·
    refine ⟨27897315017863138341348773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74392840047635035576930061 27897315017863138341348773)
    ·
      refine ⟨5230746565849338439002895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27897315017863138341348773 5230746565849338439002895)
      ·
        refine ⟨7846119848774007658504343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230746565849338439002895 7846119848774007658504343)
        ·
          refine ⟨11769179773161011487756515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846119848774007658504343 11769179773161011487756515)
          ·
            refine ⟨17653769659741517231634773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769179773161011487756515 17653769659741517231634773)
            ·
              refine ⟨51720028300023976264555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17653769659741517231634773 51720028300023976264555)
              ·
                rfl

theorem cell21_2039669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 10].length) (baseStart_2039669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039669 prefixEnd_2039669 := by exact prefixLift 2039669
  have htrace : WordTrace (prefixWord ++ tailWord_2039669) baseStart_2039669 baseEnd_2039669 := by
    simpa [prefixWord, tailWord_2039669, baseEnd_2039669] using wordTrace_append hprefix tailTrace_2039669
  have hstable : (prefixWord ++ tailWord_2039669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039669).length < 2 ^ (prefixWord ++ tailWord_2039669).sum := by decide
  have hdescent : baseEnd_2039669 < baseStart_2039669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039720 : List Nat := [2, 1, 6, 2, 2, 1, 7]
def baseStart_2039720 : Nat := 118140960795 + 2039720 * 2 ^ 59
def prefixEnd_2039720 : Nat := 4983230072969 + 3 ^ 40 * 2039720 * 2
def baseEnd_2039720 : Nat := 51721321510561225670099

theorem tailTrace_2039720 : CollatzResearch.WordTrace tailWord_2039720 prefixEnd_2039720 51721321510561225670099 := by
  unfold tailWord_2039720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37197350085225135643518307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49596466780300180858024409 37197350085225135643518307)
  ·
    refine ⟨55796025127837703465277461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37197350085225135643518307 55796025127837703465277461)
    ·
      refine ⟨2615438677867392349934881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55796025127837703465277461 2615438677867392349934881)
      ·
        refine ⟨1961579008400544262451161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2615438677867392349934881 1961579008400544262451161)
        ·
          refine ⟨1471184256300408196838371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961579008400544262451161 1471184256300408196838371)
          ·
            refine ⟨2206776384450612295257557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471184256300408196838371 2206776384450612295257557)
            ·
              refine ⟨51721321510561225670099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2206776384450612295257557 51721321510561225670099)
              ·
                rfl

theorem cell21_2039720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 7].length) (baseStart_2039720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039720 prefixEnd_2039720 := by exact prefixLift 2039720
  have htrace : WordTrace (prefixWord ++ tailWord_2039720) baseStart_2039720 baseEnd_2039720 := by
    simpa [prefixWord, tailWord_2039720, baseEnd_2039720] using wordTrace_append hprefix tailTrace_2039720
  have hstable : (prefixWord ++ tailWord_2039720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039720).length < 2 ^ (prefixWord ++ tailWord_2039720).sum := by decide
  have hdescent : baseEnd_2039720 < baseStart_2039720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039759 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_2039759 : Nat := 118140960795 + 2039759 * 2 ^ 59
def prefixEnd_2039759 : Nat := 4983230072969 + 3 ^ 40 * 2039759 * 2
def baseEnd_2039759 : Nat := 465500793926395629880811

theorem tailTrace_2039759 : CollatzResearch.WordTrace tailWord_2039759 prefixEnd_2039759 465500793926395629880811 := by
  unfold tailWord_2039759
  simp only [CollatzResearch.WordTrace]
  refine ⟨74396122617308980947706331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49597415078205987298470887 74396122617308980947706331)
  ·
    refine ⟨111594183925963471421559497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74396122617308980947706331 111594183925963471421559497)
    ·
      refine ⟨83695637944472603566169623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111594183925963471421559497 83695637944472603566169623)
      ·
        refine ⟨125543456916708905349254435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83695637944472603566169623 125543456916708905349254435)
        ·
          refine ⟨188315185375063358023881653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125543456916708905349254435 188315185375063358023881653)
          ·
            refine ⟨17654548628912189814738905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188315185375063358023881653 17654548628912189814738905)
            ·
              refine ⟨13240911471684142361054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17654548628912189814738905 13240911471684142361054179)
              ·
                refine ⟨19861367207526213541581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240911471684142361054179 19861367207526213541581269)
                ·
                  refine ⟨465500793926395629880811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19861367207526213541581269 465500793926395629880811)
                  ·
                    rfl

theorem cell21_2039759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_2039759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039759 prefixEnd_2039759 := by exact prefixLift 2039759
  have htrace : WordTrace (prefixWord ++ tailWord_2039759) baseStart_2039759 baseEnd_2039759 := by
    simpa [prefixWord, tailWord_2039759, baseEnd_2039759] using wordTrace_append hprefix tailTrace_2039759
  have hstable : (prefixWord ++ tailWord_2039759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039759).length < 2 ^ (prefixWord ++ tailWord_2039759).sum := by decide
  have hdescent : baseEnd_2039759 < baseStart_2039759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039841 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 4]
def baseStart_2039841 : Nat := 118140960795 + 2039841 * 2 ^ 59
def prefixEnd_2039841 : Nat := 4983230072969 + 3 ^ 40 * 2039841 * 2
def baseEnd_2039841 : Nat := 465519507443581709513977

theorem tailTrace_2039841 : CollatzResearch.WordTrace tailWord_2039841 prefixEnd_2039841 465519507443581709513977 := by
  unfold tailWord_2039841
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399113403011908952191377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49599408935341272634794251 74399113403011908952191377)
  ·
    refine ⟨55799335052258931714143533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74399113403011908952191377 55799335052258931714143533)
    ·
      refine ⟨20924750644597099392803825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55799335052258931714143533 20924750644597099392803825)
      ·
        refine ⟨15693562983447824544602869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20924750644597099392803825 15693562983447824544602869)
        ·
          refine ⟨1471271529698233551056519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15693562983447824544602869 1471271529698233551056519)
          ·
            refine ⟨2206907294547350326584779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471271529698233551056519 2206907294547350326584779)
            ·
              refine ⟨3310360941821025489877169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206907294547350326584779 3310360941821025489877169)
              ·
                refine ⟨2482770706365769117407877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310360941821025489877169 2482770706365769117407877)
                ·
                  refine ⟨465519507443581709513977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2482770706365769117407877 465519507443581709513977)
                  ·
                    rfl

theorem cell21_2039841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_2039841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039841 prefixEnd_2039841 := by exact prefixLift 2039841
  have htrace : WordTrace (prefixWord ++ tailWord_2039841) baseStart_2039841 baseEnd_2039841 := by
    simpa [prefixWord, tailWord_2039841, baseEnd_2039841] using wordTrace_append hprefix tailTrace_2039841
  have hstable : (prefixWord ++ tailWord_2039841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039841).length < 2 ^ (prefixWord ++ tailWord_2039841).sum := by decide
  have hdescent : baseEnd_2039841 < baseStart_2039841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039886 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2039886 : Nat := 118140960795 + 2039886 * 2 ^ 59
def prefixEnd_2039886 : Nat := 4983230072969 + 3 ^ 40 * 2039886 * 2
def baseEnd_2039886 : Nat := 465529777056671631263885

theorem tailTrace_2039886 : CollatzResearch.WordTrace tailWord_2039886 prefixEnd_2039886 465529777056671631263885 := by
  unfold tailWord_2039886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300094335981110204697439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49600503125232587758386341 9300094335981110204697439)
  ·
    refine ⟨13950141503971665307046159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300094335981110204697439 13950141503971665307046159)
    ·
      refine ⟨20925212255957497960569239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13950141503971665307046159 20925212255957497960569239)
      ·
        refine ⟨31387818383936246940853859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20925212255957497960569239 31387818383936246940853859)
        ·
          refine ⟨47081727575904370411280789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31387818383936246940853859 47081727575904370411280789)
          ·
            refine ⟨2206955980120517363028787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47081727575904370411280789 2206955980120517363028787)
            ·
              refine ⟨3310433970180776044543181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206955980120517363028787 3310433970180776044543181)
              ·
                refine ⟨1241412738817791016703693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3310433970180776044543181 1241412738817791016703693)
                ·
                  refine ⟨465529777056671631263885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241412738817791016703693 465529777056671631263885)
                  ·
                    rfl

theorem cell21_2039886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2039886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039886 prefixEnd_2039886 := by exact prefixLift 2039886
  have htrace : WordTrace (prefixWord ++ tailWord_2039886) baseStart_2039886 baseEnd_2039886 := by
    simpa [prefixWord, tailWord_2039886, baseEnd_2039886] using wordTrace_append hprefix tailTrace_2039886
  have hstable : (prefixWord ++ tailWord_2039886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039886).length < 2 ^ (prefixWord ++ tailWord_2039886).sum := by decide
  have hdescent : baseEnd_2039886 < baseStart_2039886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039914 : List Nat := [3, 1, 3, 2, 3, 1, 2, 6]
def baseStart_2039914 : Nat := 118140960795 + 2039914 * 2 ^ 59
def prefixEnd_2039914 : Nat := 4983230072969 + 3 ^ 40 * 2039914 * 2
def baseEnd_2039914 : Nat := 155178722346049934932387

theorem tailTrace_2039914 : CollatzResearch.WordTrace tailWord_2039914 prefixEnd_2039914 155178722346049934932387 := by
  unfold tailWord_2039914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18600443982936860604899699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49601183954498294946399197 18600443982936860604899699)
  ·
    refine ⟨27900665974405290907349549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18600443982936860604899699 27900665974405290907349549)
    ·
      refine ⟨10462749740401984090256081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27900665974405290907349549 10462749740401984090256081)
      ·
        refine ⟨7847062305301488067692061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10462749740401984090256081 7847062305301488067692061)
        ·
          refine ⟨2942648364488058025384523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7847062305301488067692061 2942648364488058025384523)
          ·
            refine ⟨4413972546732087038076785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942648364488058025384523 4413972546732087038076785)
            ·
              refine ⟨3310479410049065278557589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413972546732087038076785 3310479410049065278557589)
              ·
                refine ⟨155178722346049934932387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3310479410049065278557589 155178722346049934932387)
                ·
                  rfl

theorem cell21_2039914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_2039914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039914 prefixEnd_2039914 := by exact prefixLift 2039914
  have htrace : WordTrace (prefixWord ++ tailWord_2039914) baseStart_2039914 baseEnd_2039914 := by
    simpa [prefixWord, tailWord_2039914, baseEnd_2039914] using wordTrace_append hprefix tailTrace_2039914
  have hstable : (prefixWord ++ tailWord_2039914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039914).length < 2 ^ (prefixWord ++ tailWord_2039914).sum := by decide
  have hdescent : baseEnd_2039914 < baseStart_2039914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039962 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_2039962 : Nat := 118140960795 + 2039962 * 2 ^ 59
def prefixEnd_2039962 : Nat := 4983230072969 + 3 ^ 40 * 2039962 * 2
def baseEnd_2039962 : Nat := 465547121292112387997063

theorem tailTrace_2039962 : CollatzResearch.WordTrace tailWord_2039962 prefixEnd_2039962 465547121292112387997063 := by
  unfold tailWord_2039962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18600881658893386654336535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49602351090382364411564093 18600881658893386654336535)
  ·
    refine ⟨27901322488340079981504803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18600881658893386654336535 27901322488340079981504803)
    ·
      refine ⟨41851983732510119972257205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27901322488340079981504803 41851983732510119972257205)
      ·
        refine ⟨3923623474922823747399113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41851983732510119972257205 3923623474922823747399113)
        ·
          refine ⟨2942717606192117810549335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923623474922823747399113 2942717606192117810549335)
          ·
            refine ⟨4414076409288176715824003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942717606192117810549335 4414076409288176715824003)
            ·
              refine ⟨6621114613932265073736005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414076409288176715824003 6621114613932265073736005)
              ·
                refine ⟨1241458990112299701325501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6621114613932265073736005 1241458990112299701325501)
                ·
                  refine ⟨465547121292112387997063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241458990112299701325501 465547121292112387997063)
                  ·
                    rfl

theorem cell21_2039962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_2039962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2039962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2039962 prefixEnd_2039962 := by exact prefixLift 2039962
  have htrace : WordTrace (prefixWord ++ tailWord_2039962) baseStart_2039962 baseEnd_2039962 := by
    simpa [prefixWord, tailWord_2039962, baseEnd_2039962] using wordTrace_append hprefix tailTrace_2039962
  have hstable : (prefixWord ++ tailWord_2039962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039962).length < 2 ^ (prefixWord ++ tailWord_2039962).sum := by decide
  have hdescent : baseEnd_2039962 < baseStart_2039962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040021 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2040021 : Nat := 118140960795 + 2040021 * 2 ^ 59
def prefixEnd_2040021 : Nat := 4983230072969 + 3 ^ 40 * 2040021 * 2
def baseEnd_2040021 : Nat := 465560585895941396513609

theorem tailTrace_2040021 : CollatzResearch.WordTrace tailWord_2040021 prefixEnd_2040021 465560585895941396513609 := by
  unfold tailWord_2040021
  simp only [CollatzResearch.WordTrace]
  refine ⟨74405678542359799693743917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49603785694906533129162611 74405678542359799693743917)
  ·
    refine ⟨27902129453384924885153969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74405678542359799693743917 27902129453384924885153969)
    ·
      refine ⟨20926597090038693663865477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27902129453384924885153969 20926597090038693663865477)
      ·
        refine ⟨3923736954382255061974777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20926597090038693663865477 3923736954382255061974777)
        ·
          refine ⟨2942802715786691296481083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923736954382255061974777 2942802715786691296481083)
          ·
            refine ⟨4414204073680036944721625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942802715786691296481083 4414204073680036944721625)
            ·
              refine ⟨3310653055260027708541219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414204073680036944721625 3310653055260027708541219)
              ·
                refine ⟨4965979582890041562811829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310653055260027708541219 4965979582890041562811829)
                ·
                  refine ⟨465560585895941396513609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4965979582890041562811829 465560585895941396513609)
                  ·
                    rfl

theorem cell21_2040021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2040021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040021 prefixEnd_2040021 := by exact prefixLift 2040021
  have htrace : WordTrace (prefixWord ++ tailWord_2040021) baseStart_2040021 baseEnd_2040021 := by
    simpa [prefixWord, tailWord_2040021, baseEnd_2040021] using wordTrace_append hprefix tailTrace_2040021
  have hstable : (prefixWord ++ tailWord_2040021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040021).length < 2 ^ (prefixWord ++ tailWord_2040021).sum := by decide
  have hdescent : baseEnd_2040021 < baseStart_2040021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040032 : List Nat := [2, 1, 1, 3, 1, 3, 2, 8]
def baseStart_2040032 : Nat := 118140960795 + 2040032 * 2 ^ 59
def prefixEnd_2040032 : Nat := 4983230072969 + 3 ^ 40 * 2040032 * 2
def baseEnd_2040032 : Nat := 155187698748602607276751

theorem tailTrace_2040032 : CollatzResearch.WordTrace tailWord_2040032 prefixEnd_2040032 155187698748602607276751 := by
  unfold tailWord_2040032
  simp only [CollatzResearch.WordTrace]
  refine ⟨37203039872659974286197175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49604053163546632381596233 37203039872659974286197175)
  ·
    refine ⟨55804559808989961429295763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37203039872659974286197175 55804559808989961429295763)
    ·
      refine ⟨83706839713484942143943645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55804559808989961429295763 83706839713484942143943645)
      ·
        refine ⟨31390064892556853303978867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83706839713484942143943645 31390064892556853303978867)
        ·
          refine ⟨47085097338835279955968301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31390064892556853303978867 47085097338835279955968301)
          ·
            refine ⟨17656911502063229983488113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47085097338835279955968301 17656911502063229983488113)
            ·
              refine ⟨13242683626547422487616085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17656911502063229983488113 13242683626547422487616085)
              ·
                refine ⟨155187698748602607276751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13242683626547422487616085 155187698748602607276751)
                ·
                  rfl

theorem cell21_2040032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_2040032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040032 prefixEnd_2040032 := by exact prefixLift 2040032
  have htrace : WordTrace (prefixWord ++ tailWord_2040032) baseStart_2040032 baseEnd_2040032 := by
    simpa [prefixWord, tailWord_2040032, baseEnd_2040032] using wordTrace_append hprefix tailTrace_2040032
  have hstable : (prefixWord ++ tailWord_2040032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040032).length < 2 ^ (prefixWord ++ tailWord_2040032).sum := by decide
  have hdescent : baseEnd_2040032 < baseStart_2040032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040049 : List Nat := [1, 2, 2, 2, 2, 1, 6, 5]
def baseStart_2040049 : Nat := 118140960795 + 2040049 * 2 ^ 59
def prefixEnd_2040049 : Nat := 4983230072969 + 3 ^ 40 * 2040049 * 2
def baseEnd_2040049 : Nat := 155188991959139856682295

theorem tailTrace_2040049 : CollatzResearch.WordTrace tailWord_2040049 prefixEnd_2040049 155188991959139856682295 := by
  unfold tailWord_2040049
  simp only [CollatzResearch.WordTrace]
  refine ⟨74406699786258360475763201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49604466524172240317175467 74406699786258360475763201)
  ·
    refine ⟨55805024839693770356822401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74406699786258360475763201 55805024839693770356822401)
    ·
      refine ⟨41853768629770327767616801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55805024839693770356822401 41853768629770327767616801)
      ·
        refine ⟨31390326472327745825712601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41853768629770327767616801 31390326472327745825712601)
        ·
          refine ⟨23542744854245809369284451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31390326472327745825712601 23542744854245809369284451)
          ·
            refine ⟨35314117281368714053926677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542744854245809369284451 35314117281368714053926677)
            ·
              refine ⟨1655349247564158471277813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35314117281368714053926677 1655349247564158471277813)
              ·
                refine ⟨155188991959139856682295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1655349247564158471277813 155188991959139856682295)
                ·
                  rfl

theorem cell21_2040049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 5].length) (baseStart_2040049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040049 prefixEnd_2040049 := by exact prefixLift 2040049
  have htrace : WordTrace (prefixWord ++ tailWord_2040049) baseStart_2040049 baseEnd_2040049 := by
    simpa [prefixWord, tailWord_2040049, baseEnd_2040049] using wordTrace_append hprefix tailTrace_2040049
  have hstable : (prefixWord ++ tailWord_2040049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040049).length < 2 ^ (prefixWord ++ tailWord_2040049).sum := by decide
  have hdescent : baseEnd_2040049 < baseStart_2040049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040066 : List Nat := [3, 4, 1, 1, 2, 3, 7]
def baseStart_2040066 : Nat := 118140960795 + 2040066 * 2 ^ 59
def prefixEnd_2040066 : Nat := 4983230072969 + 3 ^ 40 * 2040066 * 2
def baseEnd_2040066 : Nat := 51730095056559035362613

theorem tailTrace_2040066 : CollatzResearch.WordTrace tailWord_2040066 prefixEnd_2040066 51730095056559035362613 := by
  unfold tailWord_2040066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601829956799193094783013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49604879884797848252754701 18601829956799193094783013)
  ·
    refine ⟨3487843116899848705271815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18601829956799193094783013 3487843116899848705271815)
    ·
      refine ⟨5231764675349773057907723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487843116899848705271815 5231764675349773057907723)
      ·
        refine ⟨7847647013024659586861585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5231764675349773057907723 7847647013024659586861585)
        ·
          refine ⟨5885735259768494690146189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7847647013024659586861585 5885735259768494690146189)
          ·
            refine ⟨2207150722413185508804821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5885735259768494690146189 2207150722413185508804821)
            ·
              refine ⟨51730095056559035362613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2207150722413185508804821 51730095056559035362613)
              ·
                rfl

theorem cell21_2040066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 7].length) (baseStart_2040066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040066 prefixEnd_2040066 := by exact prefixLift 2040066
  have htrace : WordTrace (prefixWord ++ tailWord_2040066) baseStart_2040066 baseEnd_2040066 := by
    simpa [prefixWord, tailWord_2040066, baseEnd_2040066] using wordTrace_append hprefix tailTrace_2040066
  have hstable : (prefixWord ++ tailWord_2040066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040066).length < 2 ^ (prefixWord ++ tailWord_2040066).sum := by decide
  have hdescent : baseEnd_2040066 < baseStart_2040066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040108 : List Nat := [2, 2, 1, 1, 1, 3, 4, 7]
def baseStart_2040108 : Nat := 118140960795 + 2040108 * 2 ^ 59
def prefixEnd_2040108 : Nat := 4983230072969 + 3 ^ 40 * 2040108 * 2
def baseEnd_2040108 : Nat := 155193480160416192854477

theorem tailTrace_2040108 : CollatzResearch.WordTrace tailWord_2040108 prefixEnd_2040108 155193480160416192854477 := by
  unfold tailWord_2040108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37204425846522306776080489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49605901128696409034773985 37204425846522306776080489)
  ·
    refine ⟨27903319384891730082060367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37204425846522306776080489 27903319384891730082060367)
    ·
      refine ⟨41854979077337595123090551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27903319384891730082060367 41854979077337595123090551)
      ·
        refine ⟨62782468616006392684635827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41854979077337595123090551 62782468616006392684635827)
        ·
          refine ⟨94173702924009589026953741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62782468616006392684635827 94173702924009589026953741)
          ·
            refine ⟨35315138596503595885107653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94173702924009589026953741 35315138596503595885107653)
            ·
              refine ⟨6621588486844424228457685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35315138596503595885107653 6621588486844424228457685)
              ·
                refine ⟨155193480160416192854477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6621588486844424228457685 155193480160416192854477)
                ·
                  rfl

theorem cell21_2040108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_2040108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040108 prefixEnd_2040108 := by exact prefixLift 2040108
  have htrace : WordTrace (prefixWord ++ tailWord_2040108) baseStart_2040108 baseEnd_2040108 := by
    simpa [prefixWord, tailWord_2040108, baseEnd_2040108] using wordTrace_append hprefix tailTrace_2040108
  have hstable : (prefixWord ++ tailWord_2040108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040108).length < 2 ^ (prefixWord ++ tailWord_2040108).sum := by decide
  have hdescent : baseEnd_2040108 < baseStart_2040108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040153 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2040153 : Nat := 118140960795 + 2040153 * 2 ^ 59
def prefixEnd_2040153 : Nat := 4983230072969 + 3 ^ 40 * 2040153 * 2
def baseEnd_2040153 : Nat := 465590710094338500313339

theorem tailTrace_2040153 : CollatzResearch.WordTrace tailWord_2040153 prefixEnd_2040153 465590710094338500313339 := by
  unfold tailWord_2040153
  simp only [CollatzResearch.WordTrace]
  refine ⟨74410492977881586237549113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49606995318587724158366075 74410492977881586237549113)
  ·
    refine ⟨55807869733411189678161835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74410492977881586237549113 55807869733411189678161835)
    ·
      refine ⟨83711804600116784517242753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55807869733411189678161835 83711804600116784517242753)
      ·
        refine ⟨62783853450087588387932065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83711804600116784517242753 62783853450087588387932065)
        ·
          refine ⟨47087890087565691290949049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62783853450087588387932065 47087890087565691290949049)
          ·
            refine ⟨35315917565674268468211787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47087890087565691290949049 35315917565674268468211787)
            ·
              refine ⟨52973876348511402702317681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35315917565674268468211787 52973876348511402702317681)
              ·
                refine ⟨39730407261383552026738261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52973876348511402702317681 39730407261383552026738261)
                ·
                  refine ⟨465590710094338500313339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39730407261383552026738261 465590710094338500313339)
                  ·
                    rfl

theorem cell21_2040153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2040153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040153 prefixEnd_2040153 := by exact prefixLift 2040153
  have htrace : WordTrace (prefixWord ++ tailWord_2040153) baseStart_2040153 baseEnd_2040153 := by
    simpa [prefixWord, tailWord_2040153, baseEnd_2040153] using wordTrace_append hprefix tailTrace_2040153
  have hstable : (prefixWord ++ tailWord_2040153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040153).length < 2 ^ (prefixWord ++ tailWord_2040153).sum := by decide
  have hdescent : baseEnd_2040153 < baseStart_2040153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040173 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2040173 : Nat := 118140960795 + 2040173 * 2 ^ 59
def prefixEnd_2040173 : Nat := 4983230072969 + 3 ^ 40 * 2040173 * 2
def baseEnd_2040173 : Nat := 465595274366822909979965

theorem tailTrace_2040173 : CollatzResearch.WordTrace tailWord_2040173 prefixEnd_2040173 465595274366822909979965 := by
  unfold tailWord_2040173
  simp only [CollatzResearch.WordTrace]
  refine ⟨74411222437809129653277173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49607481625206086435518115 74411222437809129653277173)
  ·
    refine ⟨6976052103544605904994735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74411222437809129653277173 6976052103544605904994735)
    ·
      refine ⟨10464078155316908857492103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976052103544605904994735 10464078155316908857492103)
      ·
        refine ⟨15696117232975363286238155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464078155316908857492103 15696117232975363286238155)
        ·
          refine ⟨23544175849463044929357233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15696117232975363286238155 23544175849463044929357233)
          ·
            refine ⟨17658131887097283697017925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23544175849463044929357233 17658131887097283697017925)
            ·
              refine ⟨3310899728830740693190861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17658131887097283697017925 3310899728830740693190861)
              ·
                refine ⟨1241587398311527759946573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3310899728830740693190861 1241587398311527759946573)
                ·
                  refine ⟨465595274366822909979965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241587398311527759946573 465595274366822909979965)
                  ·
                    rfl

theorem cell21_2040173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2040173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040173 prefixEnd_2040173 := by exact prefixLift 2040173
  have htrace : WordTrace (prefixWord ++ tailWord_2040173) baseStart_2040173 baseEnd_2040173 := by
    simpa [prefixWord, tailWord_2040173, baseEnd_2040173] using wordTrace_append hprefix tailTrace_2040173
  have hstable : (prefixWord ++ tailWord_2040173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040173).length < 2 ^ (prefixWord ++ tailWord_2040173).sum := by decide
  have hdescent : baseEnd_2040173 < baseStart_2040173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040187 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 4]
def baseStart_2040187 : Nat := 118140960795 + 2040187 * 2 ^ 59
def prefixEnd_2040187 : Nat := 4983230072969 + 3 ^ 40 * 2040187 * 2
def baseEnd_2040187 : Nat := 465598469357561996746603

theorem tailTrace_2040187 : CollatzResearch.WordTrace tailWord_2040187 prefixEnd_2040187 465598469357561996746603 := by
  unfold tailWord_2040187
  simp only [CollatzResearch.WordTrace]
  refine ⟨74411733059758410044286815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49607822039838940029524543 74411733059758410044286815)
  ·
    refine ⟨111617599589637615066430223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74411733059758410044286815 111617599589637615066430223)
    ·
      refine ⟨167426399384456422599645335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111617599589637615066430223 167426399384456422599645335)
      ·
        refine ⟨251139599076684633899468003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167426399384456422599645335 251139599076684633899468003)
        ·
          refine ⟨376709398615026950849202005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251139599076684633899468003 376709398615026950849202005)
          ·
            refine ⟨2207281632509923540132043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 376709398615026950849202005 2207281632509923540132043)
            ·
              refine ⟨3310922448764885310198065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207281632509923540132043 3310922448764885310198065)
              ·
                refine ⟨2483191836573663982648549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310922448764885310198065 2483191836573663982648549)
                ·
                  refine ⟨465598469357561996746603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483191836573663982648549 465598469357561996746603)
                  ·
                    rfl

theorem cell21_2040187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_2040187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040187 prefixEnd_2040187 := by exact prefixLift 2040187
  have htrace : WordTrace (prefixWord ++ tailWord_2040187) baseStart_2040187 baseEnd_2040187 := by
    simpa [prefixWord, tailWord_2040187, baseEnd_2040187] using wordTrace_append hprefix tailTrace_2040187
  have hstable : (prefixWord ++ tailWord_2040187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040187).length < 2 ^ (prefixWord ++ tailWord_2040187).sum := by decide
  have hdescent : baseEnd_2040187 < baseStart_2040187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040215 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_2040215 : Nat := 118140960795 + 2040215 * 2 ^ 59
def prefixEnd_2040215 : Nat := 4983230072969 + 3 ^ 40 * 2040215 * 2
def baseEnd_2040215 : Nat := 465604859339040170279879

theorem tailTrace_2040215 : CollatzResearch.WordTrace tailWord_2040215 prefixEnd_2040215 465604859339040170279879 := by
  unfold tailWord_2040215
  simp only [CollatzResearch.WordTrace]
  refine ⟨74412754303656970826306099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49608502869104647217537399 74412754303656970826306099)
  ·
    refine ⟨111619131455485456239459149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74412754303656970826306099 111619131455485456239459149)
    ·
      refine ⟨41857174295807046089797181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111619131455485456239459149 41857174295807046089797181)
      ·
        refine ⟨15696440360927642283673943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41857174295807046089797181 15696440360927642283673943)
        ·
          refine ⟨23544660541391463425510915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15696440360927642283673943 23544660541391463425510915)
          ·
            refine ⟨35316990812087195138266373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23544660541391463425510915 35316990812087195138266373)
            ·
              refine ⟨6621935777266349088424945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35316990812087195138266373 6621935777266349088424945)
              ·
                refine ⟨4966451832949761816318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621935777266349088424945 4966451832949761816318709)
                ·
                  refine ⟨465604859339040170279879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966451832949761816318709 465604859339040170279879)
                  ·
                    rfl

theorem cell21_2040215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_2040215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040215 prefixEnd_2040215 := by exact prefixLift 2040215
  have htrace : WordTrace (prefixWord ++ tailWord_2040215) baseStart_2040215 baseEnd_2040215 := by
    simpa [prefixWord, tailWord_2040215, baseEnd_2040215] using wordTrace_append hprefix tailTrace_2040215
  have hstable : (prefixWord ++ tailWord_2040215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040215).length < 2 ^ (prefixWord ++ tailWord_2040215).sum := by decide
  have hdescent : baseEnd_2040215 < baseStart_2040215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040218 : List Nat := [3, 1, 1, 4, 1, 4, 2, 5]
def baseStart_2040218 : Nat := 118140960795 + 2040218 * 2 ^ 59
def prefixEnd_2040218 : Nat := 4983230072969 + 3 ^ 40 * 2040218 * 2
def baseEnd_2040218 : Nat := 155201847993304277243291

theorem tailTrace_2040218 : CollatzResearch.WordTrace tailWord_2040218 prefixEnd_2040218 155201847993304277243291 := by
  unfold tailWord_2040218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18603215930661525584666327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49608575815097401559110205 18603215930661525584666327)
  ·
    refine ⟨27904823895992288376999491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18603215930661525584666327 27904823895992288376999491)
    ·
      refine ⟨41857235843988432565499237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27904823895992288376999491 41857235843988432565499237)
      ·
        refine ⟨7848231720747831106031107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41857235843988432565499237 7848231720747831106031107)
        ·
          refine ⟨11772347581121746659046661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848231720747831106031107 11772347581121746659046661)
          ·
            refine ⟨2207315171460327498571249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11772347581121746659046661 2207315171460327498571249)
            ·
              refine ⟨1655486378595245623928437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207315171460327498571249 1655486378595245623928437)
              ·
                refine ⟨155201847993304277243291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1655486378595245623928437 155201847993304277243291)
                ·
                  rfl

theorem cell21_2040218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_2040218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040218 prefixEnd_2040218 := by exact prefixLift 2040218
  have htrace : WordTrace (prefixWord ++ tailWord_2040218) baseStart_2040218 baseEnd_2040218 := by
    simpa [prefixWord, tailWord_2040218, baseEnd_2040218] using wordTrace_append hprefix tailTrace_2040218
  have hstable : (prefixWord ++ tailWord_2040218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040218).length < 2 ^ (prefixWord ++ tailWord_2040218).sum := by decide
  have hdescent : baseEnd_2040218 < baseStart_2040218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040229 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_2040229 : Nat := 118140960795 + 2040229 * 2 ^ 59
def prefixEnd_2040229 : Nat := 4983230072969 + 3 ^ 40 * 2040229 * 2
def baseEnd_2040229 : Nat := 465608054329779257046517

theorem tailTrace_2040229 : CollatzResearch.WordTrace tailWord_2040229 prefixEnd_2040229 465608054329779257046517 := by
  unfold tailWord_2040229
  simp only [CollatzResearch.WordTrace]
  refine ⟨74413264925606251217315741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49608843283737500811543827 74413264925606251217315741)
  ·
    refine ⟨27904974347102344206493403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74413264925606251217315741 27904974347102344206493403)
    ·
      refine ⟨41857461520653516309740105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27904974347102344206493403 41857461520653516309740105)
      ·
        refine ⟨31393096140490137232305079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41857461520653516309740105 31393096140490137232305079)
        ·
          refine ⟨47089644210735205848457619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31393096140490137232305079 47089644210735205848457619)
          ·
            refine ⟨70634466316102808772686429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47089644210735205848457619 70634466316102808772686429)
            ·
              refine ⟨26487924868538553289757411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70634466316102808772686429 26487924868538553289757411)
              ·
                refine ⟨39731887302807829934636117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26487924868538553289757411 39731887302807829934636117)
                ·
                  refine ⟨465608054329779257046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39731887302807829934636117 465608054329779257046517)
                  ·
                    rfl

theorem cell21_2040229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_2040229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040229 prefixEnd_2040229 := by exact prefixLift 2040229
  have htrace : WordTrace (prefixWord ++ tailWord_2040229) baseStart_2040229 baseEnd_2040229 := by
    simpa [prefixWord, tailWord_2040229, baseEnd_2040229] using wordTrace_append hprefix tailTrace_2040229
  have hstable : (prefixWord ++ tailWord_2040229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040229).length < 2 ^ (prefixWord ++ tailWord_2040229).sum := by decide
  have hdescent : baseEnd_2040229 < baseStart_2040229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040263 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 4]
def baseStart_2040263 : Nat := 118140960795 + 2040263 * 2 ^ 59
def prefixEnd_2040263 : Nat := 4983230072969 + 3 ^ 40 * 2040263 * 2
def baseEnd_2040263 : Nat := 465615813593002753479781

theorem tailTrace_2040263 : CollatzResearch.WordTrace tailWord_2040263 prefixEnd_2040263 465615813593002753479781 := by
  unfold tailWord_2040263
  simp only [CollatzResearch.WordTrace]
  refine ⟨74414505007483075024053443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49609670004988716682702295 74414505007483075024053443)
  ·
    refine ⟨111621757511224612536080165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74414505007483075024053443 111621757511224612536080165)
    ·
      refine ⟨20929079533354614850515031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111621757511224612536080165 20929079533354614850515031)
      ·
        refine ⟨31393619300031922275772547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20929079533354614850515031 31393619300031922275772547)
        ·
          refine ⟨47090428950047883413658821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31393619300031922275772547 47090428950047883413658821)
          ·
            refine ⟨8829455428133978140061029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47090428950047883413658821 8829455428133978140061029)
            ·
              refine ⟨1655522892775120901261443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8829455428133978140061029 1655522892775120901261443)
              ·
                refine ⟨2483284339162681351892165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655522892775120901261443 2483284339162681351892165)
                ·
                  refine ⟨465615813593002753479781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483284339162681351892165 465615813593002753479781)
                  ·
                    rfl

theorem cell21_2040263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4].length) (baseStart_2040263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040263 prefixEnd_2040263 := by exact prefixLift 2040263
  have htrace : WordTrace (prefixWord ++ tailWord_2040263) baseStart_2040263 baseEnd_2040263 := by
    simpa [prefixWord, tailWord_2040263, baseEnd_2040263] using wordTrace_append hprefix tailTrace_2040263
  have hstable : (prefixWord ++ tailWord_2040263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040263).length < 2 ^ (prefixWord ++ tailWord_2040263).sum := by decide
  have hdescent : baseEnd_2040263 < baseStart_2040263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040401 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 3]
def baseStart_2040401 : Nat := 118140960795 + 2040401 * 2 ^ 59
def prefixEnd_2040401 : Nat := 4983230072969 + 3 ^ 40 * 2040401 * 2
def baseEnd_2040401 : Nat := 465647307073145180179499

theorem tailTrace_2040401 : CollatzResearch.WordTrace tailWord_2040401 prefixEnd_2040401 465647307073145180179499 := by
  unfold tailWord_2040401
  simp only [CollatzResearch.WordTrace]
  refine ⟨74419538280983124592577057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49613025520655416395051371 74419538280983124592577057)
  ·
    refine ⟨55814653710737343444432793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74419538280983124592577057 55814653710737343444432793)
    ·
      refine ⟨41860990283053007583324595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55814653710737343444432793 41860990283053007583324595)
      ·
        refine ⟨62791485424579511374986893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41860990283053007583324595 62791485424579511374986893)
        ·
          refine ⟨23546807034217316765620085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62791485424579511374986893 23546807034217316765620085)
          ·
            refine ⟨2207513159457873446776883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23546807034217316765620085 2207513159457873446776883)
            ·
              refine ⟨3311269739186810170165325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207513159457873446776883 3311269739186810170165325)
              ·
                refine ⟨1241726152195053813811997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3311269739186810170165325 1241726152195053813811997)
                ·
                  refine ⟨465647307073145180179499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241726152195053813811997 465647307073145180179499)
                  ·
                    rfl

theorem cell21_2040401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_2040401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040401 prefixEnd_2040401 := by exact prefixLift 2040401
  have htrace : WordTrace (prefixWord ++ tailWord_2040401) baseStart_2040401 baseEnd_2040401 := by
    simpa [prefixWord, tailWord_2040401, baseEnd_2040401] using wordTrace_append hprefix tailTrace_2040401
  have hstable : (prefixWord ++ tailWord_2040401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040401).length < 2 ^ (prefixWord ++ tailWord_2040401).sum := by decide
  have hdescent : baseEnd_2040401 < baseStart_2040401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040418 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2040418 : Nat := 118140960795 + 2040418 * 2 ^ 59
def prefixEnd_2040418 : Nat := 4983230072969 + 3 ^ 40 * 2040418 * 2
def baseEnd_2040418 : Nat := 465651186704756928396131

theorem tailTrace_2040418 : CollatzResearch.WordTrace tailWord_2040418 prefixEnd_2040418 465651186704756928396131 := by
  unfold tailWord_2040418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605039580480384123986477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49613438881281024330630605 18605039580480384123986477)
  ·
    refine ⟨6976889842680144046494929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18605039580480384123986477 6976889842680144046494929)
    ·
      refine ⟨5232667382010108034871197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6976889842680144046494929 5232667382010108034871197)
      ·
        refine ⟨1962250268253790513076699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5232667382010108034871197 1962250268253790513076699)
        ·
          refine ⟨2943375402380685769615049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962250268253790513076699 2943375402380685769615049)
          ·
            refine ⟨2207531551785514327211287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943375402380685769615049 2207531551785514327211287)
            ·
              refine ⟨3311297327678271490816931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207531551785514327211287 3311297327678271490816931)
              ·
                refine ⟨4966945991517407236225397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311297327678271490816931 4966945991517407236225397)
                ·
                  refine ⟨465651186704756928396131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4966945991517407236225397 465651186704756928396131)
                  ·
                    rfl

theorem cell21_2040418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2040418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040418 prefixEnd_2040418 := by exact prefixLift 2040418
  have htrace : WordTrace (prefixWord ++ tailWord_2040418) baseStart_2040418 baseEnd_2040418 := by
    simpa [prefixWord, tailWord_2040418, baseEnd_2040418] using wordTrace_append hprefix tailTrace_2040418
  have hstable : (prefixWord ++ tailWord_2040418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040418).length < 2 ^ (prefixWord ++ tailWord_2040418).sum := by decide
  have hdescent : baseEnd_2040418 < baseStart_2040418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040429 : List Nat := [1, 5, 1, 1, 3, 2, 2, 6]
def baseStart_2040429 : Nat := 118140960795 + 2040429 * 2 ^ 59
def prefixEnd_2040429 : Nat := 4983230072969 + 3 ^ 40 * 2040429 * 2
def baseEnd_2040429 : Nat := 155217899018207784570925

theorem tailTrace_2040429 : CollatzResearch.WordTrace tailWord_2040429 prefixEnd_2040429 155217899018207784570925 := by
  unfold tailWord_2040429
  simp only [CollatzResearch.WordTrace]
  refine ⟨74420559524881685374596341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49613706349921123583064227 74420559524881685374596341)
  ·
    refine ⟨6976927455457658003868407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74420559524881685374596341 6976927455457658003868407)
    ·
      refine ⟨10465391183186487005802611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976927455457658003868407 10465391183186487005802611)
      ·
        refine ⟨15698086774779730508703917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465391183186487005802611 15698086774779730508703917)
        ·
          refine ⟨5886782540542398940763969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15698086774779730508703917 5886782540542398940763969)
          ·
            refine ⟨4415086905406799205572977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5886782540542398940763969 4415086905406799205572977)
            ·
              refine ⟨3311315179055099404179733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415086905406799205572977 3311315179055099404179733)
              ·
                refine ⟨155217899018207784570925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3311315179055099404179733 155217899018207784570925)
                ·
                  rfl

theorem cell21_2040429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_2040429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040429 prefixEnd_2040429 := by exact prefixLift 2040429
  have htrace : WordTrace (prefixWord ++ tailWord_2040429) baseStart_2040429 baseEnd_2040429 := by
    simpa [prefixWord, tailWord_2040429, baseEnd_2040429] using wordTrace_append hprefix tailTrace_2040429
  have hstable : (prefixWord ++ tailWord_2040429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040429).length < 2 ^ (prefixWord ++ tailWord_2040429).sum := by decide
  have hdescent : baseEnd_2040429 < baseStart_2040429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040432 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_2040432 : Nat := 118140960795 + 2040432 * 2 ^ 59
def prefixEnd_2040432 : Nat := 4983230072969 + 3 ^ 40 * 2040432 * 2
def baseEnd_2040432 : Nat := 465654381695496015162769

theorem tailTrace_2040432 : CollatzResearch.WordTrace tailWord_2040432 prefixEnd_2040432 465654381695496015162769 := by
  unfold tailWord_2040432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37210334471935408443477775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49613779295913877924637033 37210334471935408443477775)
  ·
    refine ⟨55815501707903112665216663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37210334471935408443477775 55815501707903112665216663)
    ·
      refine ⟨83723252561854668997824995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55815501707903112665216663 83723252561854668997824995)
      ·
        refine ⟨125584878842782003496737493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83723252561854668997824995 125584878842782003496737493)
        ·
          refine ⟨2943395597877703206954785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125584878842782003496737493 2943395597877703206954785)
          ·
            refine ⟨2207546698408277405216089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943395597877703206954785 2207546698408277405216089)
            ·
              refine ⟨1655660023806208053912067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207546698408277405216089 1655660023806208053912067)
              ·
                refine ⟨2483490035709312080868101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655660023806208053912067 2483490035709312080868101)
                ·
                  refine ⟨465654381695496015162769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483490035709312080868101 465654381695496015162769)
                  ·
                    rfl

theorem cell21_2040432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_2040432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040432 prefixEnd_2040432 := by exact prefixLift 2040432
  have htrace : WordTrace (prefixWord ++ tailWord_2040432) baseStart_2040432 baseEnd_2040432 := by
    simpa [prefixWord, tailWord_2040432, baseEnd_2040432] using wordTrace_append hprefix tailTrace_2040432
  have hstable : (prefixWord ++ tailWord_2040432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040432).length < 2 ^ (prefixWord ++ tailWord_2040432).sum := by decide
  have hdescent : baseEnd_2040432 < baseStart_2040432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040477 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2040477 : Nat := 118140960795 + 2040477 * 2 ^ 59
def prefixEnd_2040477 : Nat := 4983230072969 + 3 ^ 40 * 2040477 * 2
def baseEnd_2040477 : Nat := 465664651308585936912677

theorem tailTrace_2040477 : CollatzResearch.WordTrace tailWord_2040477 prefixEnd_2040477 465664651308585936912677 := by
  unfold tailWord_2040477
  simp only [CollatzResearch.WordTrace]
  refine ⟨74422310228707789572343685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49614873485805193048229123 74422310228707789572343685)
  ·
    refine ⟨13954183167882710544814441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74422310228707789572343685 13954183167882710544814441)
    ·
      refine ⟨10465637375912032908610831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13954183167882710544814441 10465637375912032908610831)
      ·
        refine ⟨15698456063868049362916247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465637375912032908610831 15698456063868049362916247)
        ·
          refine ⟨23547684095802074044374371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15698456063868049362916247 23547684095802074044374371)
          ·
            refine ⟨35321526143703111066561557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23547684095802074044374371 35321526143703111066561557)
            ·
              refine ⟨1655696537986083331245073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35321526143703111066561557 1655696537986083331245073)
              ·
                refine ⟨1241772403489562498433805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655696537986083331245073 1241772403489562498433805)
                ·
                  refine ⟨465664651308585936912677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241772403489562498433805 465664651308585936912677)
                  ·
                    rfl

theorem cell21_2040477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2040477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040477 prefixEnd_2040477 := by exact prefixLift 2040477
  have htrace : WordTrace (prefixWord ++ tailWord_2040477) baseStart_2040477 baseEnd_2040477 := by
    simpa [prefixWord, tailWord_2040477, baseEnd_2040477] using wordTrace_append hprefix tailTrace_2040477
  have hstable : (prefixWord ++ tailWord_2040477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040477).length < 2 ^ (prefixWord ++ tailWord_2040477).sum := by decide
  have hdescent : baseEnd_2040477 < baseStart_2040477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040525 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2040525 : Nat := 118140960795 + 2040525 * 2 ^ 59
def prefixEnd_2040525 : Nat := 4983230072969 + 3 ^ 40 * 2040525 * 2
def baseEnd_2040525 : Nat := 465675605562548520112579

theorem tailTrace_2040525 : CollatzResearch.WordTrace tailWord_2040525 prefixEnd_2040525 465675605562548520112579 := by
  unfold tailWord_2040525
  simp only [CollatzResearch.WordTrace]
  refine ⟨74424060932533893770091029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49616040621689262513394019 74424060932533893770091029)
  ·
    refine ⟨3488627856212526270473017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74424060932533893770091029 3488627856212526270473017)
    ·
      refine ⟨2616470892159394702854763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3488627856212526270473017 2616470892159394702854763)
      ·
        refine ⟨3924706338239092054282145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616470892159394702854763 3924706338239092054282145)
        ·
          refine ⟨2943529753679319040711609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3924706338239092054282145 2943529753679319040711609)
          ·
            refine ⟨2207647315259489280533707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943529753679319040711609 2207647315259489280533707)
            ·
              refine ⟨3311470972889233920800561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207647315259489280533707 3311470972889233920800561)
              ·
                refine ⟨2483603229666925440600421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311470972889233920800561 2483603229666925440600421)
                ·
                  refine ⟨465675605562548520112579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483603229666925440600421 465675605562548520112579)
                  ·
                    rfl

theorem cell21_2040525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2040525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040525 prefixEnd_2040525 := by exact prefixLift 2040525
  have htrace : WordTrace (prefixWord ++ tailWord_2040525) baseStart_2040525 baseEnd_2040525 := by
    simpa [prefixWord, tailWord_2040525, baseEnd_2040525] using wordTrace_append hprefix tailTrace_2040525
  have hstable : (prefixWord ++ tailWord_2040525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040525).length < 2 ^ (prefixWord ++ tailWord_2040525).sum := by decide
  have hdescent : baseEnd_2040525 < baseStart_2040525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040536 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_2040536 : Nat := 118140960795 + 2040536 * 2 ^ 59
def prefixEnd_2040536 : Nat := 4983230072969 + 3 ^ 40 * 2040536 * 2
def baseEnd_2040536 : Nat := 465678115912414945429223

theorem tailTrace_2040536 : CollatzResearch.WordTrace tailWord_2040536 prefixEnd_2040536 465678115912414945429223 := by
  unfold tailWord_2040536
  simp only [CollatzResearch.WordTrace]
  refine ⟨37212231067747021324370731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49616308090329361765827641 37212231067747021324370731)
  ·
    refine ⟨55818346601620531986556097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37212231067747021324370731 55818346601620531986556097)
    ·
      refine ⟨41863759951215398989917073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55818346601620531986556097 41863759951215398989917073)
      ·
        refine ⟨31397819963411549242437805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41863759951215398989917073 31397819963411549242437805)
        ·
          refine ⟨11774182486279330965914177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31397819963411549242437805 11774182486279330965914177)
          ·
            refine ⟨8830636864709498224435633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11774182486279330965914177 8830636864709498224435633)
            ·
              refine ⟨6622977648532123668326725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8830636864709498224435633 6622977648532123668326725)
              ·
                refine ⟨1241808309099773187811261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6622977648532123668326725 1241808309099773187811261)
                ·
                  refine ⟨465678115912414945429223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241808309099773187811261 465678115912414945429223)
                  ·
                    rfl

theorem cell21_2040536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_2040536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040536 prefixEnd_2040536 := by exact prefixLift 2040536
  have htrace : WordTrace (prefixWord ++ tailWord_2040536) baseStart_2040536 baseEnd_2040536 := by
    simpa [prefixWord, tailWord_2040536, baseEnd_2040536] using wordTrace_append hprefix tailTrace_2040536
  have hstable : (prefixWord ++ tailWord_2040536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040536).length < 2 ^ (prefixWord ++ tailWord_2040536).sum := by decide
  have hdescent : baseEnd_2040536 < baseStart_2040536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040654 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2040654 : Nat := 118140960795 + 2040654 * 2 ^ 59
def prefixEnd_2040654 : Nat := 4983230072969 + 3 ^ 40 * 2040654 * 2
def baseEnd_2040654 : Nat := 465705045120072962462315

theorem tailTrace_2040654 : CollatzResearch.WordTrace tailWord_2040654 prefixEnd_2040654 465705045120072962462315 := by
  unfold tailWord_2040654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303595743633318600192127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49619177299377699201024677 9303595743633318600192127)
  ·
    refine ⟨13955393615449977900288191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303595743633318600192127 13955393615449977900288191)
    ·
      refine ⟨20933090423174966850432287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13955393615449977900288191 20933090423174966850432287)
      ·
        refine ⟨31399635634762450275648431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20933090423174966850432287 31399635634762450275648431)
        ·
          refine ⟨47099453452143675413472647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31399635634762450275648431 47099453452143675413472647)
          ·
            refine ⟨70649180178215513120208971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47099453452143675413472647 70649180178215513120208971)
            ·
              refine ⟨105973770267323269680313457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70649180178215513120208971 105973770267323269680313457)
              ·
                refine ⟨79480327700492452260235093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105973770267323269680313457 79480327700492452260235093)
                ·
                  refine ⟨465705045120072962462315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79480327700492452260235093 465705045120072962462315)
                  ·
                    rfl

theorem cell21_2040654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2040654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040654 prefixEnd_2040654 := by exact prefixLift 2040654
  have htrace : WordTrace (prefixWord ++ tailWord_2040654) baseStart_2040654 baseEnd_2040654 := by
    simpa [prefixWord, tailWord_2040654, baseEnd_2040654] using wordTrace_append hprefix tailTrace_2040654
  have hstable : (prefixWord ++ tailWord_2040654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040654).length < 2 ^ (prefixWord ++ tailWord_2040654).sum := by decide
  have hdescent : baseEnd_2040654 < baseStart_2040654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040657 : List Nat := [1, 2, 2, 1, 6, 2, 1, 6]
def baseStart_2040657 : Nat := 118140960795 + 2040657 * 2 ^ 59
def prefixEnd_2040657 : Nat := 4983230072969 + 3 ^ 40 * 2040657 * 2
def baseEnd_2040657 : Nat := 155235243253648541304103

theorem tailTrace_2040657 : CollatzResearch.WordTrace tailWord_2040657 prefixEnd_2040657 155235243253648541304103 := by
  unfold tailWord_2040657
  simp only [CollatzResearch.WordTrace]
  refine ⟨74428875368055680313896225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49619250245370453542597483 74428875368055680313896225)
  ·
    refine ⟨55821656526041760235422169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74428875368055680313896225 55821656526041760235422169)
    ·
      refine ⟨41866242394531320176566627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55821656526041760235422169 41866242394531320176566627)
      ·
        refine ⟨62799363591796980264849941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41866242394531320176566627 62799363591796980264849941)
        ·
          refine ⟨2943720168365483449914841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62799363591796980264849941 2943720168365483449914841)
          ·
            refine ⟨2207790126274112587436131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943720168365483449914841 2207790126274112587436131)
            ·
              refine ⟨3311685189411168881154197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207790126274112587436131 3311685189411168881154197)
              ·
                refine ⟨155235243253648541304103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3311685189411168881154197 155235243253648541304103)
                ·
                  rfl

theorem cell21_2040657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 6].length) (baseStart_2040657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040657 prefixEnd_2040657 := by exact prefixLift 2040657
  have htrace : WordTrace (prefixWord ++ tailWord_2040657) baseStart_2040657 baseEnd_2040657 := by
    simpa [prefixWord, tailWord_2040657, baseEnd_2040657] using wordTrace_append hprefix tailTrace_2040657
  have hstable : (prefixWord ++ tailWord_2040657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040657).length < 2 ^ (prefixWord ++ tailWord_2040657).sum := by decide
  have hdescent : baseEnd_2040657 < baseStart_2040657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040674 : List Nat := [3, 3, 2, 1, 3, 1, 3, 5]
def baseStart_2040674 : Nat := 118140960795 + 2040674 * 2 ^ 59
def prefixEnd_2040674 : Nat := 4983230072969 + 3 ^ 40 * 2040674 * 2
def baseEnd_2040674 : Nat := 155236536464185790709647

theorem tailTrace_2040674 : CollatzResearch.WordTrace tailWord_2040674 prefixEnd_2040674 155236536464185790709647 := by
  unfold tailWord_2040674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607373852248523054316269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49619663605996061478176717 18607373852248523054316269)
  ·
    refine ⟨6977765194593196145368601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18607373852248523054316269 6977765194593196145368601)
    ·
      refine ⟨5233323895944897109026451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6977765194593196145368601 5233323895944897109026451)
      ·
        refine ⟨7849985843917345663539677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233323895944897109026451 7849985843917345663539677)
        ·
          refine ⟨2943744691469004623827379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7849985843917345663539677 2943744691469004623827379)
          ·
            refine ⟨4415617037203506935741069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943744691469004623827379 4415617037203506935741069)
            ·
              refine ⟨1655856388951315100902901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4415617037203506935741069 1655856388951315100902901)
              ·
                refine ⟨155236536464185790709647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1655856388951315100902901 155236536464185790709647)
                ·
                  rfl

theorem cell21_2040674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_2040674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040674 prefixEnd_2040674 := by exact prefixLift 2040674
  have htrace : WordTrace (prefixWord ++ tailWord_2040674) baseStart_2040674 baseEnd_2040674 := by
    simpa [prefixWord, tailWord_2040674, baseEnd_2040674] using wordTrace_append hprefix tailTrace_2040674
  have hstable : (prefixWord ++ tailWord_2040674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040674).length < 2 ^ (prefixWord ++ tailWord_2040674).sum := by decide
  have hdescent : baseEnd_2040674 < baseStart_2040674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040685 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2040685 : Nat := 118140960795 + 2040685 * 2 ^ 59
def prefixEnd_2040685 : Nat := 4983230072969 + 3 ^ 40 * 2040685 * 2
def baseEnd_2040685 : Nat := 465712119742423797445585

theorem tailTrace_2040685 : CollatzResearch.WordTrace tailWord_2040685 prefixEnd_2040685 465712119742423797445585 := by
  unfold tailWord_2040685
  simp only [CollatzResearch.WordTrace]
  refine ⟨74429896611954241095915509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49619931074636160730610339 74429896611954241095915509)
  ·
    refine ⟨6977802807370710102742079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74429896611954241095915509 6977802807370710102742079)
    ·
      refine ⟨10466704211056065154113119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6977802807370710102742079 10466704211056065154113119)
      ·
        refine ⟨15700056316584097731169679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10466704211056065154113119 15700056316584097731169679)
        ·
          refine ⟨23550084474876146596754519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15700056316584097731169679 23550084474876146596754519)
          ·
            refine ⟨35325126712314219895131779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23550084474876146596754519 35325126712314219895131779)
            ·
              refine ⟨52987690068471329842697669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35325126712314219895131779 52987690068471329842697669)
              ·
                refine ⟨9935191887838374345505813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52987690068471329842697669 9935191887838374345505813)
                ·
                  refine ⟨465712119742423797445585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9935191887838374345505813 465712119742423797445585)
                  ·
                    rfl

theorem cell21_2040685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2040685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040685 prefixEnd_2040685 := by exact prefixLift 2040685
  have htrace : WordTrace (prefixWord ++ tailWord_2040685) baseStart_2040685 baseEnd_2040685 := by
    simpa [prefixWord, tailWord_2040685, baseEnd_2040685] using wordTrace_append hprefix tailTrace_2040685
  have hstable : (prefixWord ++ tailWord_2040685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040685).length < 2 ^ (prefixWord ++ tailWord_2040685).sum := by decide
  have hdescent : baseEnd_2040685 < baseStart_2040685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040761 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_2040761 : Nat := 118140960795 + 2040761 * 2 ^ 59
def prefixEnd_2040761 : Nat := 4983230072969 + 3 ^ 40 * 2040761 * 2
def baseEnd_2040761 : Nat := 465729463977864554178763

theorem tailTrace_2040761 : CollatzResearch.WordTrace tailWord_2040761 prefixEnd_2040761 465729463977864554178763 := by
  unfold tailWord_2040761
  simp only [CollatzResearch.WordTrace]
  refine ⟨74432668559678906075682137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49621779039785937383788091 74432668559678906075682137)
  ·
    refine ⟨55824501419759179556761603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74432668559678906075682137 55824501419759179556761603)
    ·
      refine ⟨83736752129638769335142405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55824501419759179556761603 83736752129638769335142405)
      ·
        refine ⟨15700641024307269250339201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83736752129638769335142405 15700641024307269250339201)
        ·
          refine ⟨11775480768230451937754401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15700641024307269250339201 11775480768230451937754401)
          ·
            refine ⟨8831610576172838953315801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11775480768230451937754401 8831610576172838953315801)
            ·
              refine ⟨6623707932129629214986851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831610576172838953315801 6623707932129629214986851)
              ·
                refine ⟨9935561898194443822480277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623707932129629214986851 9935561898194443822480277)
                ·
                  refine ⟨465729463977864554178763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9935561898194443822480277 465729463977864554178763)
                  ·
                    rfl

theorem cell21_2040761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_2040761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040761 prefixEnd_2040761 := by exact prefixLift 2040761
  have htrace : WordTrace (prefixWord ++ tailWord_2040761) baseStart_2040761 baseEnd_2040761 := by
    simpa [prefixWord, tailWord_2040761, baseEnd_2040761] using wordTrace_append hprefix tailTrace_2040761
  have hstable : (prefixWord ++ tailWord_2040761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040761).length < 2 ^ (prefixWord ++ tailWord_2040761).sum := by decide
  have hdescent : baseEnd_2040761 < baseStart_2040761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040775 : List Nat := [1, 1, 4, 1, 1, 2, 3, 8]
def baseStart_2040775 : Nat := 118140960795 + 2040775 * 2 ^ 59
def prefixEnd_2040775 : Nat := 4983230072969 + 3 ^ 40 * 2040775 * 2
def baseEnd_2040775 : Nat := 155244219656201213648467

theorem tailTrace_2040775 : CollatzResearch.WordTrace tailWord_2040775 prefixEnd_2040775 155244219656201213648467 := by
  unfold tailWord_2040775
  simp only [CollatzResearch.WordTrace]
  refine ⟨74433179181628186466691779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49622119454418790977794519 74433179181628186466691779)
  ·
    refine ⟨111649768772442279700037669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74433179181628186466691779 111649768772442279700037669)
    ·
      refine ⟨20934331644832927443757063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111649768772442279700037669 20934331644832927443757063)
      ·
        refine ⟨31401497467249391165635595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20934331644832927443757063 31401497467249391165635595)
        ·
          refine ⟨47102246200874086748453393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31401497467249391165635595 47102246200874086748453393)
          ·
            refine ⟨35326684650655565061340045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47102246200874086748453393 35326684650655565061340045)
            ·
              refine ⟨13247506743995836898002517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35326684650655565061340045 13247506743995836898002517)
              ·
                refine ⟨155244219656201213648467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13247506743995836898002517 155244219656201213648467)
                ·
                  rfl

theorem cell21_2040775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_2040775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040775 prefixEnd_2040775 := by exact prefixLift 2040775
  have htrace : WordTrace (prefixWord ++ tailWord_2040775) baseStart_2040775 baseEnd_2040775 := by
    simpa [prefixWord, tailWord_2040775, baseEnd_2040775] using wordTrace_append hprefix tailTrace_2040775
  have hstable : (prefixWord ++ tailWord_2040775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040775).length < 2 ^ (prefixWord ++ tailWord_2040775).sum := by decide
  have hdescent : baseEnd_2040775 < baseStart_2040775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040837 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2040837 : Nat := 118140960795 + 2040837 * 2 ^ 59
def prefixEnd_2040837 : Nat := 4983230072969 + 3 ^ 40 * 2040837 * 2
def baseEnd_2040837 : Nat := 465746808213305310911941

theorem tailTrace_2040837 : CollatzResearch.WordTrace tailWord_2040837 prefixEnd_2040837 465746808213305310911941 := by
  unfold tailWord_2040837
  simp only [CollatzResearch.WordTrace]
  refine ⟨74435440507403571055448765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49623627004935714036965843 74435440507403571055448765)
  ·
    refine ⟨27913290190276339145793287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74435440507403571055448765 27913290190276339145793287)
    ·
      refine ⟨41869935285414508718689931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27913290190276339145793287 41869935285414508718689931)
      ·
        refine ⟨62804902928121763078034897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41869935285414508718689931 62804902928121763078034897)
        ·
          refine ⟨47103677196091322308526173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62804902928121763078034897 47103677196091322308526173)
          ·
            refine ⟨17663878948534245865697315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47103677196091322308526173 17663878948534245865697315)
            ·
              refine ⟨26495818422801368798545973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17663878948534245865697315 26495818422801368798545973)
              ·
                refine ⟨2483982977137628324863685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26495818422801368798545973 2483982977137628324863685)
                ·
                  refine ⟨465746808213305310911941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2483982977137628324863685 465746808213305310911941)
                  ·
                    rfl

theorem cell21_2040837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2040837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040837 prefixEnd_2040837 := by exact prefixLift 2040837
  have htrace : WordTrace (prefixWord ++ tailWord_2040837) baseStart_2040837 baseEnd_2040837 := by
    simpa [prefixWord, tailWord_2040837, baseEnd_2040837] using wordTrace_append hprefix tailTrace_2040837
  have hstable : (prefixWord ++ tailWord_2040837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040837).length < 2 ^ (prefixWord ++ tailWord_2040837).sum := by decide
  have hdescent : baseEnd_2040837 < baseStart_2040837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040868 : List Nat := [2, 3, 1, 4, 1, 2, 8]
def baseStart_2040868 : Nat := 118140960795 + 2040868 * 2 ^ 59
def prefixEnd_2040868 : Nat := 4983230072969 + 3 ^ 40 * 2040868 * 2
def baseEnd_2040868 : Nat := 51750431426184016210579

theorem tailTrace_2040868 : CollatzResearch.WordTrace tailWord_2040868 prefixEnd_2040868 51750431426184016210579 := by
  unfold tailWord_2040868
  simp only [CollatzResearch.WordTrace]
  refine ⟨37218285585145631674913629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49624380780194175566551505 37218285585145631674913629)
  ·
    refine ⟨13956857094429611878092611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37218285585145631674913629 13956857094429611878092611)
    ·
      refine ⟨20935285641644417817138917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13956857094429611878092611 20935285641644417817138917)
      ·
        refine ⟨3925366057808328340713547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20935285641644417817138917 3925366057808328340713547)
        ·
          refine ⟨5888049086712492511070321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925366057808328340713547 5888049086712492511070321)
          ·
            refine ⟨4416036815034369383302741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5888049086712492511070321 4416036815034369383302741)
            ·
              refine ⟨51750431426184016210579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4416036815034369383302741 51750431426184016210579)
              ·
                rfl

theorem cell21_2040868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 8].length) (baseStart_2040868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040868 prefixEnd_2040868 := by exact prefixLift 2040868
  have htrace : WordTrace (prefixWord ++ tailWord_2040868) baseStart_2040868 baseEnd_2040868 := by
    simpa [prefixWord, tailWord_2040868, baseEnd_2040868] using wordTrace_append hprefix tailTrace_2040868
  have hstable : (prefixWord ++ tailWord_2040868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040868).length < 2 ^ (prefixWord ++ tailWord_2040868).sum := by decide
  have hdescent : baseEnd_2040868 < baseStart_2040868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040871 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_2040871 : Nat := 118140960795 + 2040871 * 2 ^ 59
def prefixEnd_2040871 : Nat := 4983230072969 + 3 ^ 40 * 2040871 * 2
def baseEnd_2040871 : Nat := 465754567476528807345205

theorem tailTrace_2040871 : CollatzResearch.WordTrace tailWord_2040871 prefixEnd_2040871 465754567476528807345205 := by
  unfold tailWord_2040871
  simp only [CollatzResearch.WordTrace]
  refine ⟨74436680589280394862186467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49624453726186929908124311 74436680589280394862186467)
  ·
    refine ⟨111655020883920592293279701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74436680589280394862186467 111655020883920592293279701)
    ·
      refine ⟨2616914551966888881873743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 111655020883920592293279701 2616914551966888881873743)
      ·
        refine ⟨3925371827950333322810615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616914551966888881873743 3925371827950333322810615)
        ·
          refine ⟨5888057741925499984215923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925371827950333322810615 5888057741925499984215923)
          ·
            refine ⟨8832086612888249976323885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888057741925499984215923 8832086612888249976323885)
            ·
              refine ⟨3312032479833093741121457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8832086612888249976323885 3312032479833093741121457)
              ·
                refine ⟨2484024359874820305841093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312032479833093741121457 2484024359874820305841093)
                ·
                  refine ⟨465754567476528807345205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484024359874820305841093 465754567476528807345205)
                  ·
                    rfl

theorem cell21_2040871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_2040871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040871 prefixEnd_2040871 := by exact prefixLift 2040871
  have htrace : WordTrace (prefixWord ++ tailWord_2040871) baseStart_2040871 baseEnd_2040871 := by
    simpa [prefixWord, tailWord_2040871, baseEnd_2040871] using wordTrace_append hprefix tailTrace_2040871
  have hstable : (prefixWord ++ tailWord_2040871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040871).length < 2 ^ (prefixWord ++ tailWord_2040871).sum := by decide
  have hdescent : baseEnd_2040871 < baseStart_2040871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040902 : List Nat := [6, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2040902 : Nat := 118140960795 + 2040902 * 2 ^ 59
def prefixEnd_2040902 : Nat := 4983230072969 + 3 ^ 40 * 2040902 * 2
def baseEnd_2040902 : Nat := 155253880699626547442825

theorem tailTrace_2040902 : CollatzResearch.WordTrace tailWord_2040902 prefixEnd_2040902 155253880699626547442825 := by
  unfold tailWord_2040902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326181601630252723642655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49625207501445391437709973 2326181601630252723642655)
  ·
    refine ⟨3489272402445379085463983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326181601630252723642655 3489272402445379085463983)
    ·
      refine ⟨5233908603668068628195975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3489272402445379085463983 5233908603668068628195975)
      ·
        refine ⟨7850862905502102942293963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233908603668068628195975 7850862905502102942293963)
        ·
          refine ⟨11776294358253154413440945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7850862905502102942293963 11776294358253154413440945)
          ·
            refine ⟨8832220768689865810080709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11776294358253154413440945 8832220768689865810080709)
            ·
              refine ⟨1656041394129349839390133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8832220768689865810080709 1656041394129349839390133)
              ·
                refine ⟨155253880699626547442825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1656041394129349839390133 155253880699626547442825)
                ·
                  rfl

theorem cell21_2040902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2040902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040902 prefixEnd_2040902 := by exact prefixLift 2040902
  have htrace : WordTrace (prefixWord ++ tailWord_2040902) baseStart_2040902 baseEnd_2040902 := by
    simpa [prefixWord, tailWord_2040902, baseEnd_2040902] using wordTrace_append hprefix tailTrace_2040902
  have hstable : (prefixWord ++ tailWord_2040902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040902).length < 2 ^ (prefixWord ++ tailWord_2040902).sum := by decide
  have hdescent : baseEnd_2040902 < baseStart_2040902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040916 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2040916 : Nat := 118140960795 + 2040916 * 2 ^ 59
def prefixEnd_2040916 : Nat := 4983230072969 + 3 ^ 40 * 2040916 * 2
def baseEnd_2040916 : Nat := 465764837089618729095113

theorem tailTrace_2040916 : CollatzResearch.WordTrace tailWord_2040916 prefixEnd_2040916 465764837089618729095113 := by
  unfold tailWord_2040916
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219160937058683773787301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49625547916078245031716401 37219160937058683773787301)
  ·
    refine ⟨6978592675698503207585119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37219160937058683773787301 6978592675698503207585119)
    ·
      refine ⟨10467889013547754811377679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978592675698503207585119 10467889013547754811377679)
      ·
        refine ⟨15701833520321632217066519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467889013547754811377679 15701833520321632217066519)
        ·
          refine ⟨23552750280482448325599779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15701833520321632217066519 23552750280482448325599779)
          ·
            refine ⟨35329125420723672488399669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23552750280482448325599779 35329125420723672488399669)
            ·
              refine ⟨3312105508192844295787469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35329125420723672488399669 3312105508192844295787469)
              ·
                refine ⟨1242039565572316610920301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312105508192844295787469 1242039565572316610920301)
                ·
                  refine ⟨465764837089618729095113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242039565572316610920301 465764837089618729095113)
                  ·
                    rfl

theorem cell21_2040916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2040916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040916 prefixEnd_2040916 := by exact prefixLift 2040916
  have htrace : WordTrace (prefixWord ++ tailWord_2040916) baseStart_2040916 baseEnd_2040916 := by
    simpa [prefixWord, tailWord_2040916, baseEnd_2040916] using wordTrace_append hprefix tailTrace_2040916
  have hstable : (prefixWord ++ tailWord_2040916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040916).length < 2 ^ (prefixWord ++ tailWord_2040916).sum := by decide
  have hdescent : baseEnd_2040916 < baseStart_2040916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040930 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2040930 : Nat := 118140960795 + 2040930 * 2 ^ 59
def prefixEnd_2040930 : Nat := 4983230072969 + 3 ^ 40 * 2040930 * 2
def baseEnd_2040930 : Nat := 465768032080357815861751

theorem tailTrace_2040930 : CollatzResearch.WordTrace tailWord_2040930 prefixEnd_2040930 465768032080357815861751 := by
  unfold tailWord_2040930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609708124016661984646061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49625888330711098625722829 18609708124016661984646061)
  ·
    refine ⟨6978640546506248244242273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18609708124016661984646061 6978640546506248244242273)
    ·
      refine ⟨5233980409879686183181705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6978640546506248244242273 5233980409879686183181705)
      ·
        refine ⟨3925485307409764637386279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5233980409879686183181705 3925485307409764637386279)
        ·
          refine ⟨5888227961114646956079419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925485307409764637386279 5888227961114646956079419)
          ·
            refine ⟨8832341941671970434119129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888227961114646956079419 8832341941671970434119129)
            ·
              refine ⟨6624256456253977825589347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832341941671970434119129 6624256456253977825589347)
              ·
                refine ⟨9936384684380966738384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624256456253977825589347 9936384684380966738384021)
                ·
                  refine ⟨465768032080357815861751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9936384684380966738384021 465768032080357815861751)
                  ·
                    rfl

theorem cell21_2040930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2040930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040930 prefixEnd_2040930 := by exact prefixLift 2040930
  have htrace : WordTrace (prefixWord ++ tailWord_2040930) baseStart_2040930 baseEnd_2040930 := by
    simpa [prefixWord, tailWord_2040930, baseEnd_2040930] using wordTrace_append hprefix tailTrace_2040930
  have hstable : (prefixWord ++ tailWord_2040930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040930).length < 2 ^ (prefixWord ++ tailWord_2040930).sum := by decide
  have hdescent : baseEnd_2040930 < baseStart_2040930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040972 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2040972 : Nat := 118140960795 + 2040972 * 2 ^ 59
def prefixEnd_2040972 : Nat := 4983230072969 + 3 ^ 40 * 2040972 * 2
def baseEnd_2040972 : Nat := 465777617052575076161665

theorem tailTrace_2040972 : CollatzResearch.WordTrace tailWord_2040972 prefixEnd_2040972 465777617052575076161665 := by
  unfold tailWord_2040972
  simp only [CollatzResearch.WordTrace]
  refine ⟨37220182180957244555806585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49626909574609659407742113 37220182180957244555806585)
  ·
    refine ⟨27915136635717933416854939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37220182180957244555806585 27915136635717933416854939)
    ·
      refine ⟨41872704953576900125282409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27915136635717933416854939 41872704953576900125282409)
      ·
        refine ⟨31404528715182675093961807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41872704953576900125282409 31404528715182675093961807)
        ·
          refine ⟨47106793072774012640942711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31404528715182675093961807 47106793072774012640942711)
          ·
            refine ⟨70660189609161018961414067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47106793072774012640942711 70660189609161018961414067)
            ·
              refine ⟨105990284413741528442121101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70660189609161018961414067 105990284413741528442121101)
              ·
                refine ⟨39746356655153073165795413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105990284413741528442121101 39746356655153073165795413)
                ·
                  refine ⟨465777617052575076161665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39746356655153073165795413 465777617052575076161665)
                  ·
                    rfl

theorem cell21_2040972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2040972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2040972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2040972 prefixEnd_2040972 := by exact prefixLift 2040972
  have htrace : WordTrace (prefixWord ++ tailWord_2040972) baseStart_2040972 baseEnd_2040972 := by
    simpa [prefixWord, tailWord_2040972, baseEnd_2040972] using wordTrace_append hprefix tailTrace_2040972
  have hstable : (prefixWord ++ tailWord_2040972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040972).length < 2 ^ (prefixWord ++ tailWord_2040972).sum := by decide
  have hdescent : baseEnd_2040972 < baseStart_2040972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041096 : List Nat := [2, 1, 3, 2, 4, 2, 7]
def baseStart_2041096 : Nat := 118140960795 + 2041096 * 2 ^ 59
def prefixEnd_2041096 : Nat := 4983230072969 + 3 ^ 40 * 2041096 * 2
def baseEnd_2041096 : Nat := 51756212837997601788305

theorem tailTrace_2041096 : CollatzResearch.WordTrace tailWord_2041096 prefixEnd_2041096 51756212837997601788305 := by
  unfold tailWord_2041096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37222443506732629144563571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49629924675643505526084761 37222443506732629144563571)
  ·
    refine ⟨55833665260098943716845357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37222443506732629144563571 55833665260098943716845357)
    ·
      refine ⟨20937624472537103893817009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55833665260098943716845357 20937624472537103893817009)
      ·
        refine ⟨15703218354402827920362757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20937624472537103893817009 15703218354402827920362757)
        ·
          refine ⟨2944353441450530235068017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15703218354402827920362757 2944353441450530235068017)
          ·
            refine ⟨2208265081087897676301013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2944353441450530235068017 2208265081087897676301013)
            ·
              refine ⟨51756212837997601788305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2208265081087897676301013 51756212837997601788305)
              ·
                rfl

theorem cell21_2041096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 7].length) (baseStart_2041096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041096 prefixEnd_2041096 := by exact prefixLift 2041096
  have htrace : WordTrace (prefixWord ++ tailWord_2041096) baseStart_2041096 baseEnd_2041096 := by
    simpa [prefixWord, tailWord_2041096, baseEnd_2041096] using wordTrace_append hprefix tailTrace_2041096
  have hstable : (prefixWord ++ tailWord_2041096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041096).length < 2 ^ (prefixWord ++ tailWord_2041096).sum := by decide
  have hdescent : baseEnd_2041096 < baseStart_2041096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041200 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_2041200 : Nat := 118140960795 + 2041200 * 2 ^ 59
def prefixEnd_2041200 : Nat := 4983230072969 + 3 ^ 40 * 2041200 * 2
def baseEnd_2041200 : Nat := 465829649758897346361199

theorem tailTrace_2041200 : CollatzResearch.WordTrace tailWord_2041200 prefixEnd_2041200 465829649758897346361199 := by
  unfold tailWord_2041200
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224340102544242025456527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49632453470058989367275369 37224340102544242025456527)
  ·
    refine ⟨55836510153816363038184791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37224340102544242025456527 55836510153816363038184791)
    ·
      refine ⟨83754765230724544557277187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55836510153816363038184791 83754765230724544557277187)
      ·
        refine ⟨125632147846086816835915781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83754765230724544557277187 125632147846086816835915781)
        ·
          refine ⟨23556027721141278156734209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125632147846086816835915781 23556027721141278156734209)
          ·
            refine ⟨17667020790855958617550657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23556027721141278156734209 17667020790855958617550657)
            ·
              refine ⟨13250265593141968963162993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17667020790855958617550657 13250265593141968963162993)
              ·
                refine ⟨9937699194856476722372245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13250265593141968963162993 9937699194856476722372245)
                ·
                  refine ⟨465829649758897346361199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9937699194856476722372245 465829649758897346361199)
                  ·
                    rfl

theorem cell21_2041200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_2041200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041200 prefixEnd_2041200 := by exact prefixLift 2041200
  have htrace : WordTrace (prefixWord ++ tailWord_2041200) baseStart_2041200 baseEnd_2041200 := by
    simpa [prefixWord, tailWord_2041200, baseEnd_2041200] using wordTrace_append hprefix tailTrace_2041200
  have hstable : (prefixWord ++ tailWord_2041200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041200).length < 2 ^ (prefixWord ++ tailWord_2041200).sum := by decide
  have hdescent : baseEnd_2041200 < baseStart_2041200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041428 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2041428 : Nat := 118140960795 + 2041428 * 2 ^ 59
def prefixEnd_2041428 : Nat := 4983230072969 + 3 ^ 40 * 2041428 * 2
def baseEnd_2041428 : Nat := 465881682465219616560733

theorem tailTrace_2041428 : CollatzResearch.WordTrace tailWord_2041428 prefixEnd_2041428 465881682465219616560733 := by
  unfold tailWord_2041428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228498024131239495106469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49637997365508319326808625 37228498024131239495106469)
  ·
    refine ⟨6980343379524607405332463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37228498024131239495106469 6980343379524607405332463)
    ·
      refine ⟨10470515069286911107998695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980343379524607405332463 10470515069286911107998695)
      ·
        refine ⟨15705772603930366661998043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10470515069286911107998695 15705772603930366661998043)
        ·
          refine ⟨23558658905895549992997065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15705772603930366661998043 23558658905895549992997065)
          ·
            refine ⟨17668994179421662494747799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23558658905895549992997065 17668994179421662494747799)
            ·
              refine ⟨26503491269132493742121699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668994179421662494747799 26503491269132493742121699)
              ·
                refine ⟨39755236903698740613182549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26503491269132493742121699 39755236903698740613182549)
                ·
                  refine ⟨465881682465219616560733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39755236903698740613182549 465881682465219616560733)
                  ·
                    rfl

theorem cell21_2041428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2041428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041428 prefixEnd_2041428 := by exact prefixLift 2041428
  have htrace : WordTrace (prefixWord ++ tailWord_2041428) baseStart_2041428 baseEnd_2041428 := by
    simpa [prefixWord, tailWord_2041428, baseEnd_2041428] using wordTrace_append hprefix tailTrace_2041428
  have hstable : (prefixWord ++ tailWord_2041428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041428).length < 2 ^ (prefixWord ++ tailWord_2041428).sum := by decide
  have hdescent : baseEnd_2041428 < baseStart_2041428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041431 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 3]
def baseStart_2041431 : Nat := 118140960795 + 2041431 * 2 ^ 59
def prefixEnd_2041431 : Nat := 4983230072969 + 3 ^ 40 * 2041431 * 2
def baseEnd_2041431 : Nat := 465882367106092278010727

theorem tailTrace_2041431 : CollatzResearch.WordTrace tailWord_2041431 prefixEnd_2041431 465882367106092278010727 := by
  unfold tailWord_2041431
  simp only [CollatzResearch.WordTrace]
  refine ⟨74457105467251610502572147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49638070311501073668381431 74457105467251610502572147)
  ·
    refine ⟨111685658200877415753858221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74457105467251610502572147 111685658200877415753858221)
    ·
      refine ⟨41882121825329030907696833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111685658200877415753858221 41882121825329030907696833)
      ·
        refine ⟨31411591368996773180772625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41882121825329030907696833 31411591368996773180772625)
        ·
          refine ⟨23558693526747579885579469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31411591368996773180772625 23558693526747579885579469)
          ·
            refine ⟨8834510072530342457092301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23558693526747579885579469 8834510072530342457092301)
            ·
              refine ⟨3312941277198878421409613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8834510072530342457092301 3312941277198878421409613)
              ·
                refine ⟨1242352978949579408028605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312941277198878421409613 1242352978949579408028605)
                ·
                  refine ⟨465882367106092278010727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242352978949579408028605 465882367106092278010727)
                  ·
                    rfl

theorem cell21_2041431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3].length) (baseStart_2041431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041431 prefixEnd_2041431 := by exact prefixLift 2041431
  have htrace : WordTrace (prefixWord ++ tailWord_2041431) baseStart_2041431 baseEnd_2041431 := by
    simpa [prefixWord, tailWord_2041431, baseEnd_2041431] using wordTrace_append hprefix tailTrace_2041431
  have hstable : (prefixWord ++ tailWord_2041431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041431).length < 2 ^ (prefixWord ++ tailWord_2041431).sum := by decide
  have hdescent : baseEnd_2041431 < baseStart_2041431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041462 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2041462 : Nat := 118140960795 + 2041462 * 2 ^ 59
def prefixEnd_2041462 : Nat := 4983230072969 + 3 ^ 40 * 2041462 * 2
def baseEnd_2041462 : Nat := 465889441728443112993997

theorem tailTrace_2041462 : CollatzResearch.WordTrace tailWord_2041462 prefixEnd_2041462 465889441728443112993997 := by
  unfold tailWord_2041462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653639758133706424809415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49638824086759535197967093 4653639758133706424809415)
  ·
    refine ⟨6980459637200559637214123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4653639758133706424809415 6980459637200559637214123)
    ·
      refine ⟨10470689455800839455821185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980459637200559637214123 10470689455800839455821185)
      ·
        refine ⟨7853017091850629591865889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470689455800839455821185 7853017091850629591865889)
        ·
          refine ⟨5889762818887972193899417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7853017091850629591865889 5889762818887972193899417)
          ·
            refine ⟨4417322114165979145424563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889762818887972193899417 4417322114165979145424563)
            ·
              refine ⟨6625983171248968718136845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417322114165979145424563 6625983171248968718136845)
              ·
                refine ⟨2484743689218363269301317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625983171248968718136845 2484743689218363269301317)
                ·
                  refine ⟨465889441728443112993997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484743689218363269301317 465889441728443112993997)
                  ·
                    rfl

theorem cell21_2041462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2041462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041462 prefixEnd_2041462 := by exact prefixLift 2041462
  have htrace : WordTrace (prefixWord ++ tailWord_2041462) baseStart_2041462 baseEnd_2041462 := by
    simpa [prefixWord, tailWord_2041462, baseEnd_2041462] using wordTrace_append hprefix tailTrace_2041462
  have hstable : (prefixWord ++ tailWord_2041462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041462).length < 2 ^ (prefixWord ++ tailWord_2041462).sum := by decide
  have hdescent : baseEnd_2041462 < baseStart_2041462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041535 : List Nat := [1, 1, 2, 2, 2, 3, 5, 5]
def baseStart_2041535 : Nat := 118140960795 + 2041535 * 2 ^ 59
def prefixEnd_2041535 : Nat := 4983230072969 + 3 ^ 40 * 2041535 * 2
def baseEnd_2041535 : Nat := 155302033774337069425727

theorem tailTrace_2041535 : CollatzResearch.WordTrace tailWord_2041535 prefixEnd_2041535 155302033774337069425727 := by
  unfold tailWord_2041535
  simp only [CollatzResearch.WordTrace]
  refine ⟨74460898658874836264358059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49640599105916557509572039 74460898658874836264358059)
  ·
    refine ⟨111691347988312254396537089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74460898658874836264358059 111691347988312254396537089)
    ·
      refine ⟨83768510991234190797402817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111691347988312254396537089 83768510991234190797402817)
      ·
        refine ⟨62826383243425643098052113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83768510991234190797402817 62826383243425643098052113)
        ·
          refine ⟨47119787432569232323539085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62826383243425643098052113 47119787432569232323539085)
          ·
            refine ⟨17669920287213462121327157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47119787432569232323539085 17669920287213462121327157)
            ·
              refine ⟨1656555026926262073874421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17669920287213462121327157 1656555026926262073874421)
              ·
                refine ⟨155302033774337069425727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1656555026926262073874421 155302033774337069425727)
                ·
                  rfl

theorem cell21_2041535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 5].length) (baseStart_2041535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041535 prefixEnd_2041535 := by exact prefixLift 2041535
  have htrace : WordTrace (prefixWord ++ tailWord_2041535) baseStart_2041535 baseEnd_2041535 := by
    simpa [prefixWord, tailWord_2041535, baseEnd_2041535] using wordTrace_append hprefix tailTrace_2041535
  have hstable : (prefixWord ++ tailWord_2041535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041535).length < 2 ^ (prefixWord ++ tailWord_2041535).sum := by decide
  have hdescent : baseEnd_2041535 < baseStart_2041535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041580 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_2041580 : Nat := 118140960795 + 2041580 * 2 ^ 59
def prefixEnd_2041580 : Nat := 4983230072969 + 3 ^ 40 * 2041580 * 2
def baseEnd_2041580 : Nat := 465916370936101130027089

theorem tailTrace_2041580 : CollatzResearch.WordTrace tailWord_2041580 prefixEnd_2041580 465916370936101130027089 := by
  unfold tailWord_2041580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231269971855904474873097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49641693295807872633164129 37231269971855904474873097)
  ·
    refine ⟨27923452478891928356154823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37231269971855904474873097 27923452478891928356154823)
    ·
      refine ⟨41885178718337892534232235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27923452478891928356154823 41885178718337892534232235)
      ·
        refine ⟨62827768077506838801348353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41885178718337892534232235 62827768077506838801348353)
        ·
          refine ⟨47120826058130129101011265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62827768077506838801348353 47120826058130129101011265)
          ·
            refine ⟨35340619543597596825758449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47120826058130129101011265 35340619543597596825758449)
            ·
              refine ⟨26505464657698197619318837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35340619543597596825758449 26505464657698197619318837)
              ·
                refine ⟨2484887311659206026811141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26505464657698197619318837 2484887311659206026811141)
                ·
                  refine ⟨465916370936101130027089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484887311659206026811141 465916370936101130027089)
                  ·
                    rfl

theorem cell21_2041580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_2041580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041580 prefixEnd_2041580 := by exact prefixLift 2041580
  have htrace : WordTrace (prefixWord ++ tailWord_2041580) baseStart_2041580 baseEnd_2041580 := by
    simpa [prefixWord, tailWord_2041580, baseEnd_2041580] using wordTrace_append hprefix tailTrace_2041580
  have hstable : (prefixWord ++ tailWord_2041580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041580).length < 2 ^ (prefixWord ++ tailWord_2041580).sum := by decide
  have hdescent : baseEnd_2041580 < baseStart_2041580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041715 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_2041715 : Nat := 118140960795 + 2041715 * 2 ^ 59
def prefixEnd_2041715 : Nat := 4983230072969 + 3 ^ 40 * 2041715 * 2
def baseEnd_2041715 : Nat := 465947179775370895276813

theorem tailTrace_2041715 : CollatzResearch.WordTrace tailWord_2041715 prefixEnd_2041715 465947179775370895276813 := by
  unfold tailWord_2041715
  simp only [CollatzResearch.WordTrace]
  refine ⟨74467463798222727005910599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49644975865481818003940399 74467463798222727005910599)
  ·
    refine ⟨111701195697334090508865899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74467463798222727005910599 111701195697334090508865899)
    ·
      refine ⟨167551793546001135763298849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111701195697334090508865899 167551793546001135763298849)
      ·
        refine ⟨125663845159500851822474137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167551793546001135763298849 125663845159500851822474137)
        ·
          refine ⟨94247883869625638866855603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125663845159500851822474137 94247883869625638866855603)
          ·
            refine ⟨141371825804438458300283405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94247883869625638866855603 141371825804438458300283405)
            ·
              refine ⟨53014434676664421862606277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141371825804438458300283405 53014434676664421862606277)
              ·
                refine ⟨9940206501874579099238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53014434676664421862606277 9940206501874579099238677)
                ·
                  refine ⟨465947179775370895276813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9940206501874579099238677 465947179775370895276813)
                  ·
                    rfl

theorem cell21_2041715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_2041715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041715 prefixEnd_2041715 := by exact prefixLift 2041715
  have htrace : WordTrace (prefixWord ++ tailWord_2041715) baseStart_2041715 baseEnd_2041715 := by
    simpa [prefixWord, tailWord_2041715, baseEnd_2041715] using wordTrace_append hprefix tailTrace_2041715
  have hstable : (prefixWord ++ tailWord_2041715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041715).length < 2 ^ (prefixWord ++ tailWord_2041715).sum := by decide
  have hdescent : baseEnd_2041715 < baseStart_2041715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041749 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2041749 : Nat := 118140960795 + 2041749 * 2 ^ 59
def prefixEnd_2041749 : Nat := 4983230072969 + 3 ^ 40 * 2041749 * 2
def baseEnd_2041749 : Nat := 465954939038594391710077

theorem tailTrace_2041749 : CollatzResearch.WordTrace tailWord_2041749 prefixEnd_2041749 465954939038594391710077 := by
  unfold tailWord_2041749
  simp only [CollatzResearch.WordTrace]
  refine ⟨74468703880099550812648301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49645802586733033875098867 74468703880099550812648301)
  ·
    refine ⟨27925763955037331554743113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74468703880099550812648301 27925763955037331554743113)
    ·
      refine ⟨20944322966277998666057335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27925763955037331554743113 20944322966277998666057335)
      ·
        refine ⟨31416484449416997999086003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20944322966277998666057335 31416484449416997999086003)
        ·
          refine ⟨47124726674125496998629005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31416484449416997999086003 47124726674125496998629005)
          ·
            refine ⟨17671772502797061374485877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47124726674125496998629005 17671772502797061374485877)
            ·
              refine ⟨1656728672137224503858051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17671772502797061374485877 1656728672137224503858051)
              ·
                refine ⟨2485093008205836755787077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656728672137224503858051 2485093008205836755787077)
                ·
                  refine ⟨465954939038594391710077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485093008205836755787077 465954939038594391710077)
                  ·
                    rfl

theorem cell21_2041749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2041749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041749 prefixEnd_2041749 := by exact prefixLift 2041749
  have htrace : WordTrace (prefixWord ++ tailWord_2041749) baseStart_2041749 baseEnd_2041749 := by
    simpa [prefixWord, tailWord_2041749, baseEnd_2041749] using wordTrace_append hprefix tailTrace_2041749
  have hstable : (prefixWord ++ tailWord_2041749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041749).length < 2 ^ (prefixWord ++ tailWord_2041749).sum := by decide
  have hdescent : baseEnd_2041749 < baseStart_2041749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041791 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_2041791 : Nat := 118140960795 + 2041791 * 2 ^ 59
def prefixEnd_2041791 : Nat := 4983230072969 + 3 ^ 40 * 2041791 * 2
def baseEnd_2041791 : Nat := 465964524010811652009991

theorem tailTrace_2041791 : CollatzResearch.WordTrace tailWord_2041791 prefixEnd_2041791 465964524010811652009991 := by
  unfold tailWord_2041791
  simp only [CollatzResearch.WordTrace]
  refine ⟨74470235745947391985677227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49646823830631594657118151 74470235745947391985677227)
  ·
    refine ⟨111705353618921087978515841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74470235745947391985677227 111705353618921087978515841)
    ·
      refine ⟨83779015214190815983886881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111705353618921087978515841 83779015214190815983886881)
      ·
        refine ⟨62834261410643111987915161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83779015214190815983886881 62834261410643111987915161)
        ·
          refine ⟨47125696057982333990936371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62834261410643111987915161 47125696057982333990936371)
          ·
            refine ⟨70688544086973500986404557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47125696057982333990936371 70688544086973500986404557)
            ·
              refine ⟨26508204032615062869901709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70688544086973500986404557 26508204032615062869901709)
              ·
                refine ⟨9940576512230648576213141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26508204032615062869901709 9940576512230648576213141)
                ·
                  refine ⟨465964524010811652009991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9940576512230648576213141 465964524010811652009991)
                  ·
                    rfl

theorem cell21_2041791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_2041791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041791 prefixEnd_2041791 := by exact prefixLift 2041791
  have htrace : WordTrace (prefixWord ++ tailWord_2041791) baseStart_2041791 baseEnd_2041791 := by
    simpa [prefixWord, tailWord_2041791, baseEnd_2041791] using wordTrace_append hprefix tailTrace_2041791
  have hstable : (prefixWord ++ tailWord_2041791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041791).length < 2 ^ (prefixWord ++ tailWord_2041791).sum := by decide
  have hdescent : baseEnd_2041791 < baseStart_2041791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041943 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_2041943 : Nat := 118140960795 + 2041943 * 2 ^ 59
def prefixEnd_2041943 : Nat := 4983230072969 + 3 ^ 40 * 2041943 * 2
def baseEnd_2041943 : Nat := 465999212481693165476347

theorem tailTrace_2041943 : CollatzResearch.WordTrace tailWord_2041943 prefixEnd_2041943 465999212481693165476347 := by
  unfold tailWord_2041943
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475779641396721945210483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49650519760931147963473655 74475779641396721945210483)
  ·
    refine ⟨111713669462095082917815725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74475779641396721945210483 111713669462095082917815725)
    ·
      refine ⟨41892626048285656094180897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111713669462095082917815725 41892626048285656094180897)
      ·
        refine ⟨31419469536214242070635673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41892626048285656094180897 31419469536214242070635673)
        ·
          refine ⟨23564602152160681552976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31419469536214242070635673 23564602152160681552976755)
          ·
            refine ⟨35346903228241022329465133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23564602152160681552976755 35346903228241022329465133)
            ·
              refine ⟨13255088710590383373549425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35346903228241022329465133 13255088710590383373549425)
              ·
                refine ⟨9941316532942787530162069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13255088710590383373549425 9941316532942787530162069)
                ·
                  refine ⟨465999212481693165476347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9941316532942787530162069 465999212481693165476347)
                  ·
                    rfl

theorem cell21_2041943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_2041943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041943 prefixEnd_2041943 := by exact prefixLift 2041943
  have htrace : WordTrace (prefixWord ++ tailWord_2041943) baseStart_2041943 baseEnd_2041943 := by
    simpa [prefixWord, tailWord_2041943, baseEnd_2041943] using wordTrace_append hprefix tailTrace_2041943
  have hstable : (prefixWord ++ tailWord_2041943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041943).length < 2 ^ (prefixWord ++ tailWord_2041943).sum := by decide
  have hdescent : baseEnd_2041943 < baseStart_2041943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041977 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 4]
def baseStart_2041977 : Nat := 118140960795 + 2041977 * 2 ^ 59
def prefixEnd_2041977 : Nat := 4983230072969 + 3 ^ 40 * 2041977 * 2
def baseEnd_2041977 : Nat := 466006971744916661909611

theorem tailTrace_2041977 : CollatzResearch.WordTrace tailWord_2041977 prefixEnd_2041977 466006971744916661909611 := by
  unfold tailWord_2041977
  simp only [CollatzResearch.WordTrace]
  refine ⟨74477019723273545751948185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49651346482182363834632123 74477019723273545751948185)
  ·
    refine ⟨55857764792455159313961139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74477019723273545751948185 55857764792455159313961139)
    ·
      refine ⟨83786647188682738970941709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55857764792455159313961139 83786647188682738970941709)
      ·
        refine ⟨31419992695756027114103141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83786647188682738970941709 31419992695756027114103141)
        ·
          refine ⟨5891248630454255083894339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31419992695756027114103141 5891248630454255083894339)
          ·
            refine ⟨8836872945681382625841509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891248630454255083894339 8836872945681382625841509)
            ·
              refine ⟨1656913677315259242345283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8836872945681382625841509 1656913677315259242345283)
              ·
                refine ⟨2485370515972888863517925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656913677315259242345283 2485370515972888863517925)
                ·
                  refine ⟨466006971744916661909611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485370515972888863517925 466006971744916661909611)
                  ·
                    rfl

theorem cell21_2041977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_2041977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2041977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2041977 prefixEnd_2041977 := by exact prefixLift 2041977
  have htrace : WordTrace (prefixWord ++ tailWord_2041977) baseStart_2041977 baseEnd_2041977 := by
    simpa [prefixWord, tailWord_2041977, baseEnd_2041977] using wordTrace_append hprefix tailTrace_2041977
  have hstable : (prefixWord ++ tailWord_2041977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041977).length < 2 ^ (prefixWord ++ tailWord_2041977).sum := by decide
  have hdescent : baseEnd_2041977 < baseStart_2041977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042014 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2042014 : Nat := 118140960795 + 2042014 * 2 ^ 59
def prefixEnd_2042014 : Nat := 4983230072969 + 3 ^ 40 * 2042014 * 2
def baseEnd_2042014 : Nat := 466015415649012819792869

theorem tailTrace_2042014 : CollatzResearch.WordTrace tailWord_2042014 prefixEnd_2042014 466015415649012819792869 := by
  unfold tailWord_2042014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309796153017437633880637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49652246149426334047363397 9309796153017437633880637)
  ·
    refine ⟨3491173557381539112705239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9309796153017437633880637 3491173557381539112705239)
    ·
      refine ⟨5236760336072308669057859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491173557381539112705239 5236760336072308669057859)
      ·
        refine ⟨7855140504108463003586789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236760336072308669057859 7855140504108463003586789)
        ·
          refine ⟨1472838844520336813172523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7855140504108463003586789 1472838844520336813172523)
          ·
            refine ⟨2209258266780505219758785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472838844520336813172523 2209258266780505219758785)
            ·
              refine ⟨1656943700085378914819089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209258266780505219758785 1656943700085378914819089)
              ·
                refine ⟨1242707775064034186114317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656943700085378914819089 1242707775064034186114317)
                ·
                  refine ⟨466015415649012819792869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1242707775064034186114317 466015415649012819792869)
                  ·
                    rfl

theorem cell21_2042014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2042014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042014 prefixEnd_2042014 := by exact prefixLift 2042014
  have htrace : WordTrace (prefixWord ++ tailWord_2042014) baseStart_2042014 baseEnd_2042014 := by
    simpa [prefixWord, tailWord_2042014, baseEnd_2042014] using wordTrace_append hprefix tailTrace_2042014
  have hstable : (prefixWord ++ tailWord_2042014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042014).length < 2 ^ (prefixWord ++ tailWord_2042014).sum := by decide
  have hdescent : baseEnd_2042014 < baseStart_2042014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042070 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2042070 : Nat := 118140960795 + 2042070 * 2 ^ 59
def prefixEnd_2042070 : Nat := 4983230072969 + 3 ^ 40 * 2042070 * 2
def baseEnd_2042070 : Nat := 466028195611969166859421

theorem tailTrace_2042070 : CollatzResearch.WordTrace tailWord_2042070 prefixEnd_2042070 466028195611969166859421 := by
  unfold tailWord_2042070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655025731996038914692729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49653607807957748423389109 4655025731996038914692729)
  ·
    refine ⟨3491269298997029186019547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4655025731996038914692729 3491269298997029186019547)
    ·
      refine ⟨5236903948495543779029321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491269298997029186019547 5236903948495543779029321)
      ·
        refine ⟨3927677961371657834271991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236903948495543779029321 3927677961371657834271991)
        ·
          refine ⟨5891516942057486751407987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927677961371657834271991 5891516942057486751407987)
          ·
            refine ⟨8837275413086230127111981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891516942057486751407987 8837275413086230127111981)
            ·
              refine ⟨3313978279907336297666993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8837275413086230127111981 3313978279907336297666993)
              ·
                refine ⟨2485483709930502223250245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313978279907336297666993 2485483709930502223250245)
                ·
                  refine ⟨466028195611969166859421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485483709930502223250245 466028195611969166859421)
                  ·
                    rfl

theorem cell21_2042070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2042070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042070 prefixEnd_2042070 := by exact prefixLift 2042070
  have htrace : WordTrace (prefixWord ++ tailWord_2042070) baseStart_2042070 baseEnd_2042070 := by
    simpa [prefixWord, tailWord_2042070, baseEnd_2042070] using wordTrace_append hprefix tailTrace_2042070
  have hstable : (prefixWord ++ tailWord_2042070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042070).length < 2 ^ (prefixWord ++ tailWord_2042070).sum := by decide
  have hdescent : baseEnd_2042070 < baseStart_2042070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042081 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_2042081 : Nat := 118140960795 + 2042081 * 2 ^ 59
def prefixEnd_2042081 : Nat := 4983230072969 + 3 ^ 40 * 2042081 * 2
def baseEnd_2042081 : Nat := 466030705961835592176065

theorem tailTrace_2042081 : CollatzResearch.WordTrace tailWord_2042081 prefixEnd_2042081 466030705961835592176065 := by
  unfold tailWord_2042081
  simp only [CollatzResearch.WordTrace]
  refine ⟨74480812914896771513734097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49653875276597847675822731 74480812914896771513734097)
  ·
    refine ⟨55860609686172578635300573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74480812914896771513734097 55860609686172578635300573)
    ·
      refine ⟨20947728632314716988237715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55860609686172578635300573 20947728632314716988237715)
      ·
        refine ⟨31421592948472075482356573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20947728632314716988237715 31421592948472075482356573)
        ·
          refine ⟨11783097355677028305883715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31421592948472075482356573 11783097355677028305883715)
          ·
            refine ⟨17674646033515542458825573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11783097355677028305883715 17674646033515542458825573)
            ·
              refine ⟨3313996131284164211029795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17674646033515542458825573 3313996131284164211029795)
              ·
                refine ⟨4970994196926246316544693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313996131284164211029795 4970994196926246316544693)
                ·
                  refine ⟨466030705961835592176065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4970994196926246316544693 466030705961835592176065)
                  ·
                    rfl

theorem cell21_2042081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_2042081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042081 prefixEnd_2042081 := by exact prefixLift 2042081
  have htrace : WordTrace (prefixWord ++ tailWord_2042081) baseStart_2042081 baseEnd_2042081 := by
    simpa [prefixWord, tailWord_2042081, baseEnd_2042081] using wordTrace_append hprefix tailTrace_2042081
  have hstable : (prefixWord ++ tailWord_2042081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042081).length < 2 ^ (prefixWord ++ tailWord_2042081).sum := by decide
  have hdescent : baseEnd_2042081 < baseStart_2042081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042146 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2042146 : Nat := 118140960795 + 2042146 * 2 ^ 59
def prefixEnd_2042146 : Nat := 4983230072969 + 3 ^ 40 * 2042146 * 2
def baseEnd_2042146 : Nat := 466045539847409923592599

theorem tailTrace_2042146 : CollatzResearch.WordTrace tailWord_2042146 prefixEnd_2042146 466045539847409923592599 := by
  unfold tailWord_2042146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18620795914915321903712573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49655455773107525076566861 18620795914915321903712573)
  ·
    refine ⟨6982798468093245713892215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18620795914915321903712573 6982798468093245713892215)
    ·
      refine ⟨10474197702139868570838323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982798468093245713892215 10474197702139868570838323)
      ·
        refine ⟨15711296553209802856257485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474197702139868570838323 15711296553209802856257485)
        ·
          refine ⟨5891736207453676071096557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15711296553209802856257485 5891736207453676071096557)
          ·
            refine ⟨2209401077795128526661209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5891736207453676071096557 2209401077795128526661209)
            ·
              refine ⟨1657050808346346394995907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209401077795128526661209 1657050808346346394995907)
              ·
                refine ⟨2485576212519519592493861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657050808346346394995907 2485576212519519592493861)
                ·
                  refine ⟨466045539847409923592599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485576212519519592493861 466045539847409923592599)
                  ·
                    rfl

theorem cell21_2042146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2042146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042146 prefixEnd_2042146 := by exact prefixLift 2042146
  have htrace : WordTrace (prefixWord ++ tailWord_2042146) baseStart_2042146 baseEnd_2042146 := by
    simpa [prefixWord, tailWord_2042146, baseEnd_2042146] using wordTrace_append hprefix tailTrace_2042146
  have hstable : (prefixWord ++ tailWord_2042146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042146).length < 2 ^ (prefixWord ++ tailWord_2042146).sum := by decide
  have hdescent : baseEnd_2042146 < baseStart_2042146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042188 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_2042188 : Nat := 118140960795 + 2042188 * 2 ^ 59
def prefixEnd_2042188 : Nat := 4983230072969 + 3 ^ 40 * 2042188 * 2
def baseEnd_2042188 : Nat := 466055124819627183892513

theorem tailTrace_2042188 : CollatzResearch.WordTrace tailWord_2042188 prefixEnd_2042188 466055124819627183892513 := by
  unfold tailWord_2042188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242357762754564393939609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49656477017006085858586145 37242357762754564393939609)
  ·
    refine ⟨27931768322065923295454707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37242357762754564393939609 27931768322065923295454707)
    ·
      refine ⟨41897652483098884943182061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27931768322065923295454707 41897652483098884943182061)
      ·
        refine ⟨15711619681162081853693273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41897652483098884943182061 15711619681162081853693273)
        ·
          refine ⟨11783714760871561390269955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15711619681162081853693273 11783714760871561390269955)
          ·
            refine ⟨17675572141307342085404933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11783714760871561390269955 17675572141307342085404933)
            ·
              refine ⟨3314169776495126641013425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17675572141307342085404933 3314169776495126641013425)
              ·
                refine ⟨2485627332371344980760069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3314169776495126641013425 2485627332371344980760069)
                ·
                  refine ⟨466055124819627183892513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485627332371344980760069 466055124819627183892513)
                  ·
                    rfl

theorem cell21_2042188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_2042188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042188 prefixEnd_2042188 := by exact prefixLift 2042188
  have htrace : WordTrace (prefixWord ++ tailWord_2042188) baseStart_2042188 baseEnd_2042188 := by
    simpa [prefixWord, tailWord_2042188, baseEnd_2042188] using wordTrace_append hprefix tailTrace_2042188
  have hstable : (prefixWord ++ tailWord_2042188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042188).length < 2 ^ (prefixWord ++ tailWord_2042188).sum := by decide
  have hdescent : baseEnd_2042188 < baseStart_2042188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042247 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_2042247 : Nat := 118140960795 + 2042247 * 2 ^ 59
def prefixEnd_2042247 : Nat := 4983230072969 + 3 ^ 40 * 2042247 * 2
def baseEnd_2042247 : Nat := 466068589423456192409059

theorem tailTrace_2042247 : CollatzResearch.WordTrace tailWord_2042247 prefixEnd_2042247 466068589423456192409059 := by
  unfold tailWord_2042247
  simp only [CollatzResearch.WordTrace]
  refine ⟨74486867432295381864276995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49657911621530254576184663 74486867432295381864276995)
  ·
    refine ⟨111730301148443072796415493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74486867432295381864276995 111730301148443072796415493)
    ·
      refine ⟨20949431465333076149327905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111730301148443072796415493 20949431465333076149327905)
      ·
        refine ⟨15712073598999807111995929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20949431465333076149327905 15712073598999807111995929)
        ·
          refine ⟨11784055199249855333996947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15712073598999807111995929 11784055199249855333996947)
          ·
            refine ⟨17676082798874783000995421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11784055199249855333996947 17676082798874783000995421)
            ·
              refine ⟨6628531049578043625373283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17676082798874783000995421 6628531049578043625373283)
              ·
                refine ⟨9942796574367065438059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6628531049578043625373283 9942796574367065438059925)
                ·
                  refine ⟨466068589423456192409059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9942796574367065438059925 466068589423456192409059)
                  ·
                    rfl

theorem cell21_2042247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_2042247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042247 prefixEnd_2042247 := by exact prefixLift 2042247
  have htrace : WordTrace (prefixWord ++ tailWord_2042247) baseStart_2042247 baseEnd_2042247 := by
    simpa [prefixWord, tailWord_2042247, baseEnd_2042247] using wordTrace_append hprefix tailTrace_2042247
  have hstable : (prefixWord ++ tailWord_2042247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042247).length < 2 ^ (prefixWord ++ tailWord_2042247).sum := by decide
  have hdescent : baseEnd_2042247 < baseStart_2042247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042261 : List Nat := [1, 3, 2, 1, 1, 2, 1, 10]
def baseStart_2042261 : Nat := 118140960795 + 2042261 * 2 ^ 59
def prefixEnd_2042261 : Nat := 4983230072969 + 3 ^ 40 * 2042261 * 2
def baseEnd_2042261 : Nat := 155357261471398426391899

theorem tailTrace_2042261 : CollatzResearch.WordTrace tailWord_2042261 prefixEnd_2042261 155357261471398426391899 := by
  unfold tailWord_2042261
  simp only [CollatzResearch.WordTrace]
  refine ⟨74487378054244662255286637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49658252036163108170191091 74487378054244662255286637)
  ·
    refine ⟨27932766770341748345732489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74487378054244662255286637 27932766770341748345732489)
    ·
      refine ⟨20949575077756311259299367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27932766770341748345732489 20949575077756311259299367)
      ·
        refine ⟨31424362616634466888949051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20949575077756311259299367 31424362616634466888949051)
        ·
          refine ⟨47136543924951700333423577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31424362616634466888949051 47136543924951700333423577)
          ·
            refine ⟨35352407943713775250067683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47136543924951700333423577 35352407943713775250067683)
            ·
              refine ⟨53028611915570662875101525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35352407943713775250067683 53028611915570662875101525)
              ·
                refine ⟨155357261471398426391899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53028611915570662875101525 155357261471398426391899)
                ·
                  rfl

theorem cell21_2042261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_2042261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042261 prefixEnd_2042261 := by exact prefixLift 2042261
  have htrace : WordTrace (prefixWord ++ tailWord_2042261) baseStart_2042261 baseEnd_2042261 := by
    simpa [prefixWord, tailWord_2042261, baseEnd_2042261] using wordTrace_append hprefix tailTrace_2042261
  have hstable : (prefixWord ++ tailWord_2042261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042261).length < 2 ^ (prefixWord ++ tailWord_2042261).sum := by decide
  have hdescent : baseEnd_2042261 < baseStart_2042261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042337 : List Nat := [1, 2, 3, 1, 2, 2, 1, 9]
def baseStart_2042337 : Nat := 118140960795 + 2042337 * 2 ^ 59
def prefixEnd_2042337 : Nat := 4983230072969 + 3 ^ 40 * 2042337 * 2
def baseEnd_2042337 : Nat := 155363042883212011969625

theorem tailTrace_2042337 : CollatzResearch.WordTrace tailWord_2042337 prefixEnd_2042337 155363042883212011969625 := by
  unfold tailWord_2042337
  simp only [CollatzResearch.WordTrace]
  refine ⟨74490150001969327235053265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49660100001312884823368843 74490150001969327235053265)
  ·
    refine ⟨55867612501476995426289949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74490150001969327235053265 55867612501476995426289949)
    ·
      refine ⟨20950354688053873284858731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55867612501476995426289949 20950354688053873284858731)
      ·
        refine ⟨31425532032080809927288097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20950354688053873284858731 31425532032080809927288097)
        ·
          refine ⟨23569149024060607445466073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31425532032080809927288097 23569149024060607445466073)
          ·
            refine ⟨17676861768045455584099555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23569149024060607445466073 17676861768045455584099555)
            ·
              refine ⟨26515292652068183376149333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17676861768045455584099555 26515292652068183376149333)
              ·
                refine ⟨155363042883212011969625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26515292652068183376149333 155363042883212011969625)
                ·
                  rfl

theorem cell21_2042337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_2042337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042337 prefixEnd_2042337 := by exact prefixLift 2042337
  have htrace : WordTrace (prefixWord ++ tailWord_2042337) baseStart_2042337 baseEnd_2042337 := by
    simpa [prefixWord, tailWord_2042337, baseEnd_2042337] using wordTrace_append hprefix tailTrace_2042337
  have hstable : (prefixWord ++ tailWord_2042337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042337).length < 2 ^ (prefixWord ++ tailWord_2042337).sum := by decide
  have hdescent : baseEnd_2042337 < baseStart_2042337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042354 : List Nat := [3, 2, 1, 4, 2, 9]
def baseStart_2042354 : Nat := 118140960795 + 2042354 * 2 ^ 59
def prefixEnd_2042354 : Nat := 4983230072969 + 3 ^ 40 * 2042354 * 2
def baseEnd_2042354 : Nat := 17262704010416584597241

theorem tailTrace_2042354 : CollatzResearch.WordTrace tailWord_2042354 prefixEnd_2042354 17262704010416584597241 := by
  unfold tailWord_2042354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622692510726934784605529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49660513361938492758948077 18622692510726934784605529)
  ·
    refine ⟨13967019383045201088454147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18622692510726934784605529 13967019383045201088454147)
    ·
      refine ⟨20950529074567801632681221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13967019383045201088454147 20950529074567801632681221)
      ·
        refine ⟨3928224201481462806127729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20950529074567801632681221 3928224201481462806127729)
        ·
          refine ⟨2946168151111097104595797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3928224201481462806127729 2946168151111097104595797)
          ·
            refine ⟨17262704010416584597241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2946168151111097104595797 17262704010416584597241)
            ·
              rfl

theorem cell21_2042354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 9].length) (baseStart_2042354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042354 prefixEnd_2042354 := by exact prefixLift 2042354
  have htrace : WordTrace (prefixWord ++ tailWord_2042354) baseStart_2042354 baseEnd_2042354 := by
    simpa [prefixWord, tailWord_2042354, baseEnd_2042354] using wordTrace_append hprefix tailTrace_2042354
  have hstable : (prefixWord ++ tailWord_2042354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042354).length < 2 ^ (prefixWord ++ tailWord_2042354).sum := by decide
  have hdescent : baseEnd_2042354 < baseStart_2042354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042388 : List Nat := [2, 4, 3, 1, 1, 2, 3, 5]
def baseStart_2042388 : Nat := 118140960795 + 2042388 * 2 ^ 59
def prefixEnd_2042388 : Nat := 4983230072969 + 3 ^ 40 * 2042388 * 2
def baseEnd_2042388 : Nat := 155366922514823760186257

theorem tailTrace_2042388 : CollatzResearch.WordTrace tailWord_2042388 prefixEnd_2042388 155366922514823760186257 := by
  unfold tailWord_2042388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37246005062392281472579909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49661340083189708630106545 37246005062392281472579909)
  ·
    refine ⟨6983625949198552776108733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37246005062392281472579909 6983625949198552776108733)
    ·
      refine ⟨2618859730949457291040775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6983625949198552776108733 2618859730949457291040775)
      ·
        refine ⟨3928289596424185936561163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618859730949457291040775 3928289596424185936561163)
        ·
          refine ⟨5892434394636278904841745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928289596424185936561163 5892434394636278904841745)
          ·
            refine ⟨4419325795977209178631309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5892434394636278904841745 4419325795977209178631309)
            ·
              refine ⟨1657247173491453441986741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419325795977209178631309 1657247173491453441986741)
              ·
                refine ⟨155366922514823760186257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657247173491453441986741 155366922514823760186257)
                ·
                  rfl

theorem cell21_2042388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_2042388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042388 prefixEnd_2042388 := by exact prefixLift 2042388
  have htrace : WordTrace (prefixWord ++ tailWord_2042388) baseStart_2042388 baseEnd_2042388 := by
    simpa [prefixWord, tailWord_2042388, baseEnd_2042388] using wordTrace_append hprefix tailTrace_2042388
  have hstable : (prefixWord ++ tailWord_2042388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042388).length < 2 ^ (prefixWord ++ tailWord_2042388).sum := by decide
  have hdescent : baseEnd_2042388 < baseStart_2042388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042433 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 4]
def baseStart_2042433 : Nat := 118140960795 + 2042433 * 2 ^ 59
def prefixEnd_2042433 : Nat := 4983230072969 + 3 ^ 40 * 2042433 * 2
def baseEnd_2042433 : Nat := 466111037157561202308679

theorem tailTrace_2042433 : CollatzResearch.WordTrace tailWord_2042433 prefixEnd_2042433 466111037157561202308679 := by
  unfold tailWord_2042433
  simp only [CollatzResearch.WordTrace]
  refine ⟨74493651409621535630547953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49662434273081023753698635 74493651409621535630547953)
  ·
    refine ⟨55870238557216151722910965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74493651409621535630547953 55870238557216151722910965)
    ·
      refine ⟨5237834864739014224022903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55870238557216151722910965 5237834864739014224022903)
      ·
        refine ⟨7856752297108521336034355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237834864739014224022903 7856752297108521336034355)
        ·
          refine ⟨11785128445662782004051533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7856752297108521336034355 11785128445662782004051533)
          ·
            refine ⟨4419423167123543251519325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11785128445662782004051533 4419423167123543251519325)
            ·
              refine ⟨1657283687671328719319747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419423167123543251519325 1657283687671328719319747)
              ·
                refine ⟨2485925531506993078979621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657283687671328719319747 2485925531506993078979621)
                ·
                  refine ⟨466111037157561202308679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485925531506993078979621 466111037157561202308679)
                  ·
                    rfl

theorem cell21_2042433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_2042433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042433 prefixEnd_2042433 := by exact prefixLift 2042433
  have htrace : WordTrace (prefixWord ++ tailWord_2042433) baseStart_2042433 baseEnd_2042433 := by
    simpa [prefixWord, tailWord_2042433, baseEnd_2042433] using wordTrace_append hprefix tailTrace_2042433
  have hstable : (prefixWord ++ tailWord_2042433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042433).length < 2 ^ (prefixWord ++ tailWord_2042433).sum := by decide
  have hdescent : baseEnd_2042433 < baseStart_2042433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042444 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_2042444 : Nat := 118140960795 + 2042444 * 2 ^ 59
def prefixEnd_2042444 : Nat := 4983230072969 + 3 ^ 40 * 2042444 * 2
def baseEnd_2042444 : Nat := 466113547507427627625323

theorem tailTrace_2042444 : CollatzResearch.WordTrace tailWord_2042444 prefixEnd_2042444 466113547507427627625323 := by
  unfold tailWord_2042444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37247026306290842254599193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49662701741721123006132257 37247026306290842254599193)
  ·
    refine ⟨27935269729718131690949395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37247026306290842254599193 27935269729718131690949395)
    ·
      refine ⟨41902904594577197536424093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27935269729718131690949395 41902904594577197536424093)
      ·
        refine ⟨15713589222966449076159035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41902904594577197536424093 15713589222966449076159035)
        ·
          refine ⟨23570383834449673614238553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15713589222966449076159035 23570383834449673614238553)
          ·
            refine ⟨17677787875837255210678915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23570383834449673614238553 17677787875837255210678915)
            ·
              refine ⟨26516681813755882816018373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677787875837255210678915 26516681813755882816018373)
              ·
                refine ⟨4971877840079228028003445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26516681813755882816018373 4971877840079228028003445)
                ·
                  refine ⟨466113547507427627625323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4971877840079228028003445 466113547507427627625323)
                  ·
                    rfl

theorem cell21_2042444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_2042444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042444 prefixEnd_2042444 := by exact prefixLift 2042444
  have htrace : WordTrace (prefixWord ++ tailWord_2042444) baseStart_2042444 baseEnd_2042444 := by
    simpa [prefixWord, tailWord_2042444, baseEnd_2042444] using wordTrace_append hprefix tailTrace_2042444
  have hstable : (prefixWord ++ tailWord_2042444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042444).length < 2 ^ (prefixWord ++ tailWord_2042444).sum := by decide
  have hdescent : baseEnd_2042444 < baseStart_2042444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042478 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2042478 : Nat := 118140960795 + 2042478 * 2 ^ 59
def prefixEnd_2042478 : Nat := 4983230072969 + 3 ^ 40 * 2042478 * 2
def baseEnd_2042478 : Nat := 466121306770651124058587

theorem tailTrace_2042478 : CollatzResearch.WordTrace tailWord_2042478 prefixEnd_2042478 466121306770651124058587 := by
  unfold tailWord_2042478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311911586807313539492011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49663528462972338877290725 9311911586807313539492011)
  ·
    refine ⟨13967867380210970309238017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9311911586807313539492011 13967867380210970309238017)
    ·
      refine ⟨10475900535158227731928513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13967867380210970309238017 10475900535158227731928513)
      ·
        refine ⟨7856925401368670798946385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10475900535158227731928513 7856925401368670798946385)
        ·
          refine ⟨5892694051026503099209789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7856925401368670798946385 5892694051026503099209789)
          ·
            refine ⟨2209760269134938662203671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5892694051026503099209789 2209760269134938662203671)
            ·
              refine ⟨3314640403702407993305507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209760269134938662203671 3314640403702407993305507)
              ·
                refine ⟨4971960605553611989958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314640403702407993305507 4971960605553611989958261)
                ·
                  refine ⟨466121306770651124058587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4971960605553611989958261 466121306770651124058587)
                  ·
                    rfl

theorem cell21_2042478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2042478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042478 prefixEnd_2042478 := by exact prefixLift 2042478
  have htrace : WordTrace (prefixWord ++ tailWord_2042478) baseStart_2042478 baseEnd_2042478 := by
    simpa [prefixWord, tailWord_2042478, baseEnd_2042478] using wordTrace_append hprefix tailTrace_2042478
  have hstable : (prefixWord ++ tailWord_2042478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042478).length < 2 ^ (prefixWord ++ tailWord_2042478).sum := by decide
  have hdescent : baseEnd_2042478 < baseStart_2042478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042489 : List Nat := [1, 2, 1, 3, 3, 2, 1, 8]
def baseStart_2042489 : Nat := 118140960795 + 2042489 * 2 ^ 59
def prefixEnd_2042489 : Nat := 4983230072969 + 3 ^ 40 * 2042489 * 2
def baseEnd_2042489 : Nat := 155374605706839183125077

theorem tailTrace_2042489 : CollatzResearch.WordTrace tailWord_2042489 prefixEnd_2042489 155374605706839183125077 := by
  unfold tailWord_2042489
  simp only [CollatzResearch.WordTrace]
  refine ⟨74495693897418657194586521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49663795931612438129724347 74495693897418657194586521)
  ·
    refine ⟨55871770423063992895939891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74495693897418657194586521 55871770423063992895939891)
    ·
      refine ⟨83807655634595989343909837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55871770423063992895939891 83807655634595989343909837)
      ·
        refine ⟨31427870862973496003966189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83807655634595989343909837 31427870862973496003966189)
        ·
          refine ⟨11785451573615061001487321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31427870862973496003966189 11785451573615061001487321)
          ·
            refine ⟨8839088680211295751115491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11785451573615061001487321 8839088680211295751115491)
            ·
              refine ⟨13258633020316943626673237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839088680211295751115491 13258633020316943626673237)
              ·
                refine ⟨155374605706839183125077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13258633020316943626673237 155374605706839183125077)
                ·
                  rfl

theorem cell21_2042489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_2042489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042489 prefixEnd_2042489 := by exact prefixLift 2042489
  have htrace : WordTrace (prefixWord ++ tailWord_2042489) baseStart_2042489 baseEnd_2042489 := by
    simpa [prefixWord, tailWord_2042489, baseEnd_2042489] using wordTrace_append hprefix tailTrace_2042489
  have hstable : (prefixWord ++ tailWord_2042489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042489).length < 2 ^ (prefixWord ++ tailWord_2042489).sum := by decide
  have hdescent : baseEnd_2042489 < baseStart_2042489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042492 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_2042492 : Nat := 118140960795 + 2042492 * 2 ^ 59
def prefixEnd_2042492 : Nat := 4983230072969 + 3 ^ 40 * 2042492 * 2
def baseEnd_2042492 : Nat := 466124501761390210825225

theorem tailTrace_2042492 : CollatzResearch.WordTrace tailWord_2042492 prefixEnd_2042492 466124501761390210825225 := by
  unfold tailWord_2042492
  simp only [CollatzResearch.WordTrace]
  refine ⟨37247901658203894353472865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49663868877605192471297153 37247901658203894353472865)
  ·
    refine ⟨27935926243652920765104649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37247901658203894353472865 27935926243652920765104649)
    ·
      refine ⟨20951944682739690573828487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27935926243652920765104649 20951944682739690573828487)
      ·
        refine ⟨31427917024109535860742731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20951944682739690573828487 31427917024109535860742731)
        ·
          refine ⟨47141875536164303791114097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31427917024109535860742731 47141875536164303791114097)
          ·
            refine ⟨35356406652123227843335573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47141875536164303791114097 35356406652123227843335573)
            ·
              refine ⟨1657331561818276305156355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35356406652123227843335573 1657331561818276305156355)
              ·
                refine ⟨2485997342727414457734533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657331561818276305156355 2485997342727414457734533)
                ·
                  refine ⟨466124501761390210825225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485997342727414457734533 466124501761390210825225)
                  ·
                    rfl

theorem cell21_2042492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_2042492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042492 prefixEnd_2042492 := by exact prefixLift 2042492
  have htrace : WordTrace (prefixWord ++ tailWord_2042492) baseStart_2042492 baseEnd_2042492 := by
    simpa [prefixWord, tailWord_2042492, baseEnd_2042492] using wordTrace_append hprefix tailTrace_2042492
  have hstable : (prefixWord ++ tailWord_2042492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042492).length < 2 ^ (prefixWord ++ tailWord_2042492).sum := by decide
  have hdescent : baseEnd_2042492 < baseStart_2042492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042596 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2042596 : Nat := 118140960795 + 2042596 * 2 ^ 59
def prefixEnd_2042596 : Nat := 4983230072969 + 3 ^ 40 * 2042596 * 2
def baseEnd_2042596 : Nat := 466148235978309141091679

theorem tailTrace_2042596 : CollatzResearch.WordTrace tailWord_2042596 prefixEnd_2042596 466148235978309141091679 := by
  unfold tailWord_2042596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249798254015507234365821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49666397672020676312487761 37249798254015507234365821)
  ·
    refine ⟨13968674345255815212887183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37249798254015507234365821 13968674345255815212887183)
    ·
      refine ⟨20953011517883722819330775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968674345255815212887183 20953011517883722819330775)
      ·
        refine ⟨31429517276825584228996163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953011517883722819330775 31429517276825584228996163)
        ·
          refine ⟨47144275915238376343494245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31429517276825584228996163 47144275915238376343494245)
          ·
            refine ⟨8839551734107195564405171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47144275915238376343494245 8839551734107195564405171)
            ·
              refine ⟨13259327601160793346607757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839551734107195564405171 13259327601160793346607757)
              ·
                refine ⟨4972247850435297504977909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13259327601160793346607757 4972247850435297504977909)
                ·
                  refine ⟨466148235978309141091679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4972247850435297504977909 466148235978309141091679)
                  ·
                    rfl

theorem cell21_2042596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2042596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042596 prefixEnd_2042596 := by exact prefixLift 2042596
  have htrace : WordTrace (prefixWord ++ tailWord_2042596) baseStart_2042596 baseEnd_2042596 := by
    simpa [prefixWord, tailWord_2042596, baseEnd_2042596] using wordTrace_append hprefix tailTrace_2042596
  have hstable : (prefixWord ++ tailWord_2042596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042596).length < 2 ^ (prefixWord ++ tailWord_2042596).sum := by decide
  have hdescent : baseEnd_2042596 < baseStart_2042596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042647 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 3]
def baseStart_2042647 : Nat := 118140960795 + 2042647 * 2 ^ 59
def prefixEnd_2042647 : Nat := 4983230072969 + 3 ^ 40 * 2042647 * 2
def baseEnd_2042647 : Nat := 466159874873144385741575

theorem tailTrace_2042647 : CollatzResearch.WordTrace tailWord_2042647 prefixEnd_2042647 466159874873144385741575 := by
  unfold tailWord_2042647
  simp only [CollatzResearch.WordTrace]
  refine ⟨74501456630846250178838195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49667637753897500119225463 74501456630846250178838195)
  ·
    refine ⟨111752184946269375268257293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74501456630846250178838195 111752184946269375268257293)
    ·
      refine ⟨41907069354851015725596485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111752184946269375268257293 41907069354851015725596485)
      ·
        refine ⟨7857575504034565448549341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41907069354851015725596485 7857575504034565448549341)
        ·
          refine ⟨2946590814012962043206003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7857575504034565448549341 2946590814012962043206003)
          ·
            refine ⟨4419886221019443064809005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946590814012962043206003 4419886221019443064809005)
            ·
              refine ⟨1657457332882291149303377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4419886221019443064809005 1657457332882291149303377)
              ·
                refine ⟨1243092999661718361977533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657457332882291149303377 1243092999661718361977533)
                ·
                  refine ⟨466159874873144385741575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243092999661718361977533 466159874873144385741575)
                  ·
                    rfl

theorem cell21_2042647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 3].length) (baseStart_2042647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042647 prefixEnd_2042647 := by exact prefixLift 2042647
  have htrace : WordTrace (prefixWord ++ tailWord_2042647) baseStart_2042647 baseEnd_2042647 := by
    simpa [prefixWord, tailWord_2042647, baseEnd_2042647] using wordTrace_append hprefix tailTrace_2042647
  have hstable : (prefixWord ++ tailWord_2042647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042647).length < 2 ^ (prefixWord ++ tailWord_2042647).sum := by decide
  have hdescent : baseEnd_2042647 < baseStart_2042647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042658 : List Nat := [3, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2042658 : Nat := 118140960795 + 2042658 * 2 ^ 59
def prefixEnd_2042658 : Nat := 4983230072969 + 3 ^ 40 * 2042658 * 2
def baseEnd_2042658 : Nat := 155387461741003603686073

theorem tailTrace_2042658 : CollatzResearch.WordTrace tailWord_2042658 prefixEnd_2042658 155387461741003603686073 := by
  unfold tailWord_2042658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625464458451599764372157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49667905222537599371659085 18625464458451599764372157)
  ·
    refine ⟨6984549171919349911639559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18625464458451599764372157 6984549171919349911639559)
    ·
      refine ⟨10476823757879024867459339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984549171919349911639559 10476823757879024867459339)
      ·
        refine ⟨15715235636818537301189009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476823757879024867459339 15715235636818537301189009)
        ·
          refine ⟨11786426727613902975891757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15715235636818537301189009 11786426727613902975891757)
          ·
            refine ⟨4419910022855213615959409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11786426727613902975891757 4419910022855213615959409)
            ·
              refine ⟨3314932517141410211969557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419910022855213615959409 3314932517141410211969557)
              ·
                refine ⟨155387461741003603686073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3314932517141410211969557 155387461741003603686073)
                ·
                  rfl

theorem cell21_2042658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2042658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042658 prefixEnd_2042658 := by exact prefixLift 2042658
  have htrace : WordTrace (prefixWord ++ tailWord_2042658) baseStart_2042658 baseEnd_2042658 := by
    simpa [prefixWord, tailWord_2042658, baseEnd_2042658] using wordTrace_append hprefix tailTrace_2042658
  have hstable : (prefixWord ++ tailWord_2042658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042658).length < 2 ^ (prefixWord ++ tailWord_2042658).sum := by decide
  have hdescent : baseEnd_2042658 < baseStart_2042658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042731 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_2042731 : Nat := 118140960795 + 2042731 * 2 ^ 59
def prefixEnd_2042731 : Nat := 4983230072969 + 3 ^ 40 * 2042731 * 2
def baseEnd_2042731 : Nat := 466179044817578906341403

theorem tailTrace_2042731 : CollatzResearch.WordTrace tailWord_2042731 prefixEnd_2042731 466179044817578906341403 := by
  unfold tailWord_2042731
  simp only [CollatzResearch.WordTrace]
  refine ⟨74504520362541932524896047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49669680241694621683264031 74504520362541932524896047)
  ·
    refine ⟨111756780543812898787344071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74504520362541932524896047 111756780543812898787344071)
    ·
      refine ⟨167635170815719348181016107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111756780543812898787344071 167635170815719348181016107)
      ·
        refine ⟨251452756223579022271524161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167635170815719348181016107 251452756223579022271524161)
        ·
          refine ⟨188589567167684266703643121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251452756223579022271524161 188589567167684266703643121)
          ·
            refine ⟨141442175375763200027732341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188589567167684266703643121 141442175375763200027732341)
            ·
              refine ⟨13260203941477800002599907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141442175375763200027732341 13260203941477800002599907)
              ·
                refine ⟨19890305912216700003899861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13260203941477800002599907 19890305912216700003899861)
                ·
                  refine ⟨466179044817578906341403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19890305912216700003899861 466179044817578906341403)
                  ·
                    rfl

theorem cell21_2042731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_2042731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042731 prefixEnd_2042731 := by exact prefixLift 2042731
  have htrace : WordTrace (prefixWord ++ tailWord_2042731) baseStart_2042731 baseEnd_2042731 := by
    simpa [prefixWord, tailWord_2042731, baseEnd_2042731] using wordTrace_append hprefix tailTrace_2042731
  have hstable : (prefixWord ++ tailWord_2042731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042731).length < 2 ^ (prefixWord ++ tailWord_2042731).sum := by decide
  have hdescent : baseEnd_2042731 < baseStart_2042731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042807 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_2042807 : Nat := 118140960795 + 2042807 * 2 ^ 59
def prefixEnd_2042807 : Nat := 4983230072969 + 3 ^ 40 * 2042807 * 2
def baseEnd_2042807 : Nat := 466196389053019663074581

theorem tailTrace_2042807 : CollatzResearch.WordTrace tailWord_2042807 prefixEnd_2042807 466196389053019663074581 := by
  unfold tailWord_2042807
  simp only [CollatzResearch.WordTrace]
  refine ⟨74507292310266597504662675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49671528206844398336441783 74507292310266597504662675)
  ·
    refine ⟨111760938465399896256994013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74507292310266597504662675 111760938465399896256994013)
    ·
      refine ⟨41910351924524961096372755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111760938465399896256994013 41910351924524961096372755)
      ·
        refine ⟨62865527886787441644559133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41910351924524961096372755 62865527886787441644559133)
        ·
          refine ⟨23574572957545290616709675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62865527886787441644559133 23574572957545290616709675)
          ·
            refine ⟨35361859436317935925064513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23574572957545290616709675 35361859436317935925064513)
            ·
              refine ⟨26521394577238451943798385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35361859436317935925064513 26521394577238451943798385)
              ·
                refine ⟨19891045932928838957848789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26521394577238451943798385 19891045932928838957848789)
                ·
                  refine ⟨466196389053019663074581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19891045932928838957848789 466196389053019663074581)
                  ·
                    rfl

theorem cell21_2042807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_2042807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042807 prefixEnd_2042807 := by exact prefixLift 2042807
  have htrace : WordTrace (prefixWord ++ tailWord_2042807) baseStart_2042807 baseEnd_2042807 := by
    simpa [prefixWord, tailWord_2042807, baseEnd_2042807] using wordTrace_append hprefix tailTrace_2042807
  have hstable : (prefixWord ++ tailWord_2042807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042807).length < 2 ^ (prefixWord ++ tailWord_2042807).sum := by decide
  have hdescent : baseEnd_2042807 < baseStart_2042807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042917 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 3]
def baseStart_2042917 : Nat := 118140960795 + 2042917 * 2 ^ 59
def prefixEnd_2042917 : Nat := 4983230072969 + 3 ^ 40 * 2042917 * 2
def baseEnd_2042917 : Nat := 466221492551683916241023

theorem tailTrace_2042917 : CollatzResearch.WordTrace tailWord_2042917 prefixEnd_2042917 466221492551683916241023 := by
  unfold tailWord_2042917
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511304339868086291167005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49674202893245390860778003 74511304339868086291167005)
  ·
    refine ⟨27941739127450532359187627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74511304339868086291167005 27941739127450532359187627)
    ·
      refine ⟨41912608691175798538781441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27941739127450532359187627 41912608691175798538781441)
      ·
        refine ⟨31434456518381848904086081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41912608691175798538781441 31434456518381848904086081)
        ·
          refine ⟨23575842388786386678064561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31434456518381848904086081 23575842388786386678064561)
          ·
            refine ⟨17681881791589790008548421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23575842388786386678064561 17681881791589790008548421)
            ·
              refine ⟨3315352835923085626602829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17681881791589790008548421 3315352835923085626602829)
              ·
                refine ⟨1243257313471157109976061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315352835923085626602829 1243257313471157109976061)
                ·
                  refine ⟨466221492551683916241023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243257313471157109976061 466221492551683916241023)
                  ·
                    rfl

theorem cell21_2042917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_2042917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042917 prefixEnd_2042917 := by exact prefixLift 2042917
  have htrace : WordTrace (prefixWord ++ tailWord_2042917) baseStart_2042917 baseEnd_2042917 := by
    simpa [prefixWord, tailWord_2042917, baseEnd_2042917] using wordTrace_append hprefix tailTrace_2042917
  have hstable : (prefixWord ++ tailWord_2042917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042917).length < 2 ^ (prefixWord ++ tailWord_2042917).sum := by decide
  have hdescent : baseEnd_2042917 < baseStart_2042917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042928 : List Nat := [2, 1, 1, 1, 2, 4, 10]
def baseStart_2042928 : Nat := 118140960795 + 2042928 * 2 ^ 59
def prefixEnd_2042928 : Nat := 4983230072969 + 3 ^ 40 * 2042928 * 2
def baseEnd_2042928 : Nat := 51802666989061149061963

theorem tailTrace_2042928 : CollatzResearch.WordTrace tailWord_2042928 prefixEnd_2042928 51802666989061149061963 := by
  unfold tailWord_2042928
  simp only [CollatzResearch.WordTrace]
  refine ⟨37255852771414117584908719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49674470361885490113211625 37255852771414117584908719)
  ·
    refine ⟨55883779157121176377363079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37255852771414117584908719 55883779157121176377363079)
    ·
      refine ⟨83825668735681764566044619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55883779157121176377363079 83825668735681764566044619)
      ·
        refine ⟨125738503103522646849066929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83825668735681764566044619 125738503103522646849066929)
        ·
          refine ⟨94303877327641985136800197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125738503103522646849066929 94303877327641985136800197)
          ·
            refine ⟨17681976998932872213150037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94303877327641985136800197 17681976998932872213150037)
            ·
              refine ⟨51802666989061149061963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17681976998932872213150037 51802666989061149061963)
              ·
                rfl

theorem cell21_2042928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 10].length) (baseStart_2042928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042928 prefixEnd_2042928 := by exact prefixLift 2042928
  have htrace : WordTrace (prefixWord ++ tailWord_2042928) baseStart_2042928 baseEnd_2042928 := by
    simpa [prefixWord, tailWord_2042928, baseEnd_2042928] using wordTrace_append hprefix tailTrace_2042928
  have hstable : (prefixWord ++ tailWord_2042928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042928).length < 2 ^ (prefixWord ++ tailWord_2042928).sum := by decide
  have hdescent : baseEnd_2042928 < baseStart_2042928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042934 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2042934 : Nat := 118140960795 + 2042934 * 2 ^ 59
def prefixEnd_2042934 : Nat := 4983230072969 + 3 ^ 40 * 2042934 * 2
def baseEnd_2042934 : Nat := 466225372183295664457655

theorem tailTrace_2042934 : CollatzResearch.WordTrace tailWord_2042934 prefixEnd_2042934 466225372183295664457655 := by
  unfold tailWord_2042934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656995273800406137158491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49674616253870998796357237 4656995273800406137158491)
  ·
    refine ⟨6985492910700609205737737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656995273800406137158491 6985492910700609205737737)
    ·
      refine ⟨5239119683025456904303303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6985492910700609205737737 5239119683025456904303303)
      ·
        refine ⟨7858679524538185356454955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5239119683025456904303303 7858679524538185356454955)
        ·
          refine ⟨11788019286807278034682433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858679524538185356454955 11788019286807278034682433)
          ·
            refine ⟨8841014465105458526011825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11788019286807278034682433 8841014465105458526011825)
            ·
              refine ⟨6630760848829093894508869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841014465105458526011825 6630760848829093894508869)
              ·
                refine ⟨1243267659155455105220413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6630760848829093894508869 1243267659155455105220413)
                ·
                  refine ⟨466225372183295664457655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243267659155455105220413 466225372183295664457655)
                  ·
                    rfl

theorem cell21_2042934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2042934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042934 prefixEnd_2042934 := by exact prefixLift 2042934
  have htrace : WordTrace (prefixWord ++ tailWord_2042934) baseStart_2042934 baseEnd_2042934 := by
    simpa [prefixWord, tailWord_2042934, baseEnd_2042934] using wordTrace_append hprefix tailTrace_2042934
  have hstable : (prefixWord ++ tailWord_2042934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042934).length < 2 ^ (prefixWord ++ tailWord_2042934).sum := by decide
  have hdescent : baseEnd_2042934 < baseStart_2042934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042962 : List Nat := [3, 2, 2, 1, 3, 1, 4, 5]
def baseStart_2042962 : Nat := 118140960795 + 2042962 * 2 ^ 59
def prefixEnd_2042962 : Nat := 4983230072969 + 3 ^ 40 * 2042962 * 2
def baseEnd_2042962 : Nat := 155410587388257945996977

theorem tailTrace_2042962 : CollatzResearch.WordTrace tailWord_2042962 prefixEnd_2042962 155410587388257945996977 := by
  unfold tailWord_2042962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628236406176264744138785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49675297083136705984370093 18628236406176264744138785)
  ·
    refine ⟨13971177304632198558104089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18628236406176264744138785 13971177304632198558104089)
    ·
      refine ⟨10478382978474148918578067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13971177304632198558104089 10478382978474148918578067)
      ·
        refine ⟨15717574467711223377867101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478382978474148918578067 15717574467711223377867101)
        ·
          refine ⟨5894090425391708766700163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15717574467711223377867101 5894090425391708766700163)
          ·
            refine ⟨8841135638087563150050245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894090425391708766700163 8841135638087563150050245)
            ·
              refine ⟨1657712932141418090634421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8841135638087563150050245 1657712932141418090634421)
              ·
                refine ⟨155410587388257945996977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657712932141418090634421 155410587388257945996977)
                ·
                  rfl

theorem cell21_2042962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_2042962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2042962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2042962 prefixEnd_2042962 := by exact prefixLift 2042962
  have htrace : WordTrace (prefixWord ++ tailWord_2042962) baseStart_2042962 baseEnd_2042962 := by
    simpa [prefixWord, tailWord_2042962, baseEnd_2042962] using wordTrace_append hprefix tailTrace_2042962
  have hstable : (prefixWord ++ tailWord_2042962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042962).length < 2 ^ (prefixWord ++ tailWord_2042962).sum := by decide
  have hdescent : baseEnd_2042962 < baseStart_2042962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043080 : List Nat := [2, 1, 3, 1, 2, 1, 2, 9]
def baseStart_2043080 : Nat := 118140960795 + 2043080 * 2 ^ 59
def prefixEnd_2043080 : Nat := 4983230072969 + 3 ^ 40 * 2043080 * 2
def baseEnd_2043080 : Nat := 155419563790810618341341

theorem tailTrace_2043080 : CollatzResearch.WordTrace tailWord_2043080 prefixEnd_2043080 155419563790810618341341 := by
  unfold tailWord_2043080
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258624719138782564675347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49678166292185043419567129 37258624719138782564675347)
  ·
    refine ⟨55887937078708173847013021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37258624719138782564675347 55887937078708173847013021)
    ·
      refine ⟨20957976404515565192629883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55887937078708173847013021 20957976404515565192629883)
      ·
        refine ⟨31436964606773347788944825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957976404515565192629883 31436964606773347788944825)
        ·
          refine ⟨23577723455080010841708619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31436964606773347788944825 23577723455080010841708619)
          ·
            refine ⟨35366585182620016262562929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23577723455080010841708619 35366585182620016262562929)
            ·
              refine ⟨26524938886965012196922197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35366585182620016262562929 26524938886965012196922197)
              ·
                refine ⟨155419563790810618341341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26524938886965012196922197 155419563790810618341341)
                ·
                  rfl

theorem cell21_2043080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_2043080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043080 prefixEnd_2043080 := by exact prefixLift 2043080
  have htrace : WordTrace (prefixWord ++ tailWord_2043080) baseStart_2043080 baseEnd_2043080 := by
    simpa [prefixWord, tailWord_2043080, baseEnd_2043080] using wordTrace_append hprefix tailTrace_2043080
  have hstable : (prefixWord ++ tailWord_2043080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043080).length < 2 ^ (prefixWord ++ tailWord_2043080).sum := by decide
  have hdescent : baseEnd_2043080 < baseStart_2043080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043086 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_2043086 : Nat := 118140960795 + 2043086 * 2 ^ 59
def prefixEnd_2043086 : Nat := 4983230072969 + 3 ^ 40 * 2043086 * 2
def baseEnd_2043086 : Nat := 466260060654177177924011

theorem tailTrace_2043086 : CollatzResearch.WordTrace tailWord_2043086 prefixEnd_2043086 466260060654177177924011 := by
  unfold tailWord_2043086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314683534531978519258639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49678312184170552102712741 9314683534531978519258639)
  ·
    refine ⟨13972025301797967778887959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9314683534531978519258639 13972025301797967778887959)
    ·
      refine ⟨20958037952696951668331939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13972025301797967778887959 20958037952696951668331939)
      ·
        refine ⟨31437056929045427502497909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20958037952696951668331939 31437056929045427502497909)
        ·
          refine ⟨2947224087098008828359179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31437056929045427502497909 2947224087098008828359179)
          ·
            refine ⟨4420836130647013242538769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947224087098008828359179 4420836130647013242538769)
            ·
              refine ⟨3315627097985259931904077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420836130647013242538769 3315627097985259931904077)
              ·
                refine ⟨1243360161744472474464029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315627097985259931904077 1243360161744472474464029)
                ·
                  refine ⟨466260060654177177924011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243360161744472474464029 466260060654177177924011)
                  ·
                    rfl

theorem cell21_2043086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_2043086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043086 prefixEnd_2043086 := by exact prefixLift 2043086
  have htrace : WordTrace (prefixWord ++ tailWord_2043086) baseStart_2043086 baseEnd_2043086 := by
    simpa [prefixWord, tailWord_2043086, baseEnd_2043086] using wordTrace_append hprefix tailTrace_2043086
  have hstable : (prefixWord ++ tailWord_2043086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043086).length < 2 ^ (prefixWord ++ tailWord_2043086).sum := by decide
  have hdescent : baseEnd_2043086 < baseStart_2043086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043162 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_2043162 : Nat := 118140960795 + 2043162 * 2 ^ 59
def prefixEnd_2043162 : Nat := 4983230072969 + 3 ^ 40 * 2043162 * 2
def baseEnd_2043162 : Nat := 466277404889617934657189

theorem tailTrace_2043162 : CollatzResearch.WordTrace tailWord_2043162 prefixEnd_2043162 466277404889617934657189 := by
  unfold tailWord_2043162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18630060055995123283458935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49680160149320328755890493 18630060055995123283458935)
  ·
    refine ⟨27945090083992684925188403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18630060055995123283458935 27945090083992684925188403)
    ·
      refine ⟨41917635125989027387782605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945090083992684925188403 41917635125989027387782605)
      ·
        refine ⟨15719113172245885270418477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41917635125989027387782605 15719113172245885270418477)
        ·
          refine ⟨5894667439592206976406929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15719113172245885270418477 5894667439592206976406929)
          ·
            refine ⟨4421000579694155232305197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894667439592206976406929 4421000579694155232305197)
            ·
              refine ⟨1657875217385308212114449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4421000579694155232305197 1657875217385308212114449)
              ·
                refine ⟨1243406413038981159085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657875217385308212114449 1243406413038981159085837)
                ·
                  refine ⟨466277404889617934657189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243406413038981159085837 466277404889617934657189)
                  ·
                    rfl

theorem cell21_2043162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_2043162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043162 prefixEnd_2043162 := by exact prefixLift 2043162
  have htrace : WordTrace (prefixWord ++ tailWord_2043162) baseStart_2043162 baseEnd_2043162 := by
    simpa [prefixWord, tailWord_2043162, baseEnd_2043162] using wordTrace_append hprefix tailTrace_2043162
  have hstable : (prefixWord ++ tailWord_2043162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043162).length < 2 ^ (prefixWord ++ tailWord_2043162).sum := by decide
  have hdescent : baseEnd_2043162 < baseStart_2043162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043173 : List Nat := [1, 3, 1, 2, 4, 2, 2, 6]
def baseStart_2043173 : Nat := 118140960795 + 2043173 * 2 ^ 59
def prefixEnd_2043173 : Nat := 4983230072969 + 3 ^ 40 * 2043173 * 2
def baseEnd_2043173 : Nat := 155426638413161453324611

theorem tailTrace_2043173 : CollatzResearch.WordTrace tailWord_2043173 prefixEnd_2043173 155426638413161453324611 := by
  unfold tailWord_2043173
  simp only [CollatzResearch.WordTrace]
  refine ⟨74520641426940642012486173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49680427617960428008324115 74520641426940642012486173)
  ·
    refine ⟨27945240535102740754682315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74520641426940642012486173 27945240535102740754682315)
    ·
      refine ⟨41917860802654111132023473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945240535102740754682315 41917860802654111132023473)
      ·
        refine ⟨31438395601990583349017605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41917860802654111132023473 31438395601990583349017605)
        ·
          refine ⟨5894699175373234377940801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31438395601990583349017605 5894699175373234377940801)
          ·
            refine ⟨4421024381529925783455601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894699175373234377940801 4421024381529925783455601)
            ·
              refine ⟨3315768286147444337591701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421024381529925783455601 3315768286147444337591701)
              ·
                refine ⟨155426638413161453324611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3315768286147444337591701 155426638413161453324611)
                ·
                  rfl

theorem cell21_2043173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_2043173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043173 prefixEnd_2043173 := by exact prefixLift 2043173
  have htrace : WordTrace (prefixWord ++ tailWord_2043173) baseStart_2043173 baseEnd_2043173 := by
    simpa [prefixWord, tailWord_2043173, baseEnd_2043173] using wordTrace_append hprefix tailTrace_2043173
  have hstable : (prefixWord ++ tailWord_2043173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043173).length < 2 ^ (prefixWord ++ tailWord_2043173).sum := by decide
  have hdescent : baseEnd_2043173 < baseStart_2043173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043176 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_2043176 : Nat := 118140960795 + 2043176 * 2 ^ 59
def prefixEnd_2043176 : Nat := 4983230072969 + 3 ^ 40 * 2043176 * 2
def baseEnd_2043176 : Nat := 466280599880357021423827

theorem tailTrace_2043176 : CollatzResearch.WordTrace tailWord_2043176 prefixEnd_2043176 466280599880357021423827 := by
  unfold tailWord_2043176
  simp only [CollatzResearch.WordTrace]
  refine ⟨37260375422964886762422691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49680500563953182349896921 37260375422964886762422691)
  ·
    refine ⟨55890563134447330143634037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37260375422964886762422691 55890563134447330143634037)
    ·
      refine ⟨5239740293854437200965691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55890563134447330143634037 5239740293854437200965691)
      ·
        refine ⟨7859610440781655801448537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5239740293854437200965691 7859610440781655801448537)
        ·
          refine ⟨5894707830586241851086403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7859610440781655801448537 5894707830586241851086403)
          ·
            refine ⟨8842061745879362776629605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894707830586241851086403 8842061745879362776629605)
            ·
              refine ⟨1657886577352380520618051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8842061745879362776629605 1657886577352380520618051)
              ·
                refine ⟨2486829866028570780927077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657886577352380520618051 2486829866028570780927077)
                ·
                  refine ⟨466280599880357021423827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486829866028570780927077 466280599880357021423827)
                  ·
                    rfl

theorem cell21_2043176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_2043176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043176 prefixEnd_2043176 := by exact prefixLift 2043176
  have htrace : WordTrace (prefixWord ++ tailWord_2043176) baseStart_2043176 baseEnd_2043176 := by
    simpa [prefixWord, tailWord_2043176, baseEnd_2043176] using wordTrace_append hprefix tailTrace_2043176
  have hstable : (prefixWord ++ tailWord_2043176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043176).length < 2 ^ (prefixWord ++ tailWord_2043176).sum := by decide
  have hdescent : baseEnd_2043176 < baseStart_2043176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043213 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2043213 : Nat := 118140960795 + 2043213 * 2 ^ 59
def prefixEnd_2043213 : Nat := 4983230072969 + 3 ^ 40 * 2043213 * 2
def baseEnd_2043213 : Nat := 466289043784453179307085

theorem tailTrace_2043213 : CollatzResearch.WordTrace tailWord_2043213 prefixEnd_2043213 466289043784453179307085 := by
  unfold tailWord_2043213
  simp only [CollatzResearch.WordTrace]
  refine ⟨74522100346795728843942293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49681400231197152562628195 74522100346795728843942293)
  ·
    refine ⟨3493223453756049789559795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74522100346795728843942293 3493223453756049789559795)
    ·
      refine ⟨5239835180634074684339693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3493223453756049789559795 5239835180634074684339693)
      ·
        refine ⟨1964938192737778006627385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5239835180634074684339693 1964938192737778006627385)
        ·
          refine ⟨1473703644553333504970539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964938192737778006627385 1473703644553333504970539)
          ·
            refine ⟨2210555466830000257455809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473703644553333504970539 2210555466830000257455809)
            ·
              refine ⟨1657916600122500193091857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210555466830000257455809 1657916600122500193091857)
              ·
                refine ⟨1243437450091875144818893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657916600122500193091857 1243437450091875144818893)
                ·
                  refine ⟨466289043784453179307085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243437450091875144818893 466289043784453179307085)
                  ·
                    rfl

theorem cell21_2043213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2043213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043213 prefixEnd_2043213 := by exact prefixLift 2043213
  have htrace : WordTrace (prefixWord ++ tailWord_2043213) baseStart_2043213 baseEnd_2043213 := by
    simpa [prefixWord, tailWord_2043213, baseEnd_2043213] using wordTrace_append hprefix tailTrace_2043213
  have hstable : (prefixWord ++ tailWord_2043213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043213).length < 2 ^ (prefixWord ++ tailWord_2043213).sum := by decide
  have hdescent : baseEnd_2043213 < baseStart_2043213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043221 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 3]
def baseStart_2043221 : Nat := 118140960795 + 2043221 * 2 ^ 59
def prefixEnd_2043221 : Nat := 4983230072969 + 3 ^ 40 * 2043221 * 2
def baseEnd_2043221 : Nat := 466290869493446943173735

theorem tailTrace_2043221 : CollatzResearch.WordTrace tailWord_2043221 prefixEnd_2043221 466290869493446943173735 := by
  unfold tailWord_2043221
  simp only [CollatzResearch.WordTrace]
  refine ⟨74522392130766746210233517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49681594753844497473489011 74522392130766746210233517)
  ·
    refine ⟨27945897049037529828837569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74522392130766746210233517 27945897049037529828837569)
    ·
      refine ⟨20959422786778147371628177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27945897049037529828837569 20959422786778147371628177)
      ·
        refine ⟨15719567090083610528721133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20959422786778147371628177 15719567090083610528721133)
        ·
          refine ⟨5894837658781353948270425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15719567090083610528721133 5894837658781353948270425)
          ·
            refine ⟨4421128244086015461202819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894837658781353948270425 4421128244086015461202819)
            ·
              refine ⟨6631692366129023191804229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421128244086015461202819 6631692366129023191804229)
              ·
                refine ⟨1243442318649191848463293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6631692366129023191804229 1243442318649191848463293)
                ·
                  refine ⟨466290869493446943173735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243442318649191848463293 466290869493446943173735)
                  ·
                    rfl

theorem cell21_2043221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_2043221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043221 prefixEnd_2043221 := by exact prefixLift 2043221
  have htrace : WordTrace (prefixWord ++ tailWord_2043221) baseStart_2043221 baseEnd_2043221 := by
    simpa [prefixWord, tailWord_2043221, baseEnd_2043221] using wordTrace_append hprefix tailTrace_2043221
  have hstable : (prefixWord ++ tailWord_2043221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043221).length < 2 ^ (prefixWord ++ tailWord_2043221).sum := by decide
  have hdescent : baseEnd_2043221 < baseStart_2043221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043266 : List Nat := [3, 4, 2, 1, 1, 2, 8]
def baseStart_2043266 : Nat := 118140960795 + 2043266 * 2 ^ 59
def prefixEnd_2043266 : Nat := 4983230072969 + 3 ^ 40 * 2043266 * 2
def baseEnd_2043266 : Nat := 51811237678504096102627

theorem tailTrace_2043266 : CollatzResearch.WordTrace tailWord_2043266 prefixEnd_2043266 51811237678504096102627 := by
  unfold tailWord_2043266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631008353900929723905413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49682688943735812597081101 18631008353900929723905413)
  ·
    refine ⟨3493314066356424323232265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18631008353900929723905413 3493314066356424323232265)
    ·
      refine ⟨2619985549767318242424199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3493314066356424323232265 2619985549767318242424199)
      ·
        refine ⟨3929978324650977363636299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619985549767318242424199 3929978324650977363636299)
        ·
          refine ⟨5894967486976466045454449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929978324650977363636299 5894967486976466045454449)
          ·
            refine ⟨4421225615232349534090837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894967486976466045454449 4421225615232349534090837)
            ·
              refine ⟨51811237678504096102627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4421225615232349534090837 51811237678504096102627)
              ·
                rfl

theorem cell21_2043266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 8].length) (baseStart_2043266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043266 prefixEnd_2043266 := by exact prefixLift 2043266
  have htrace : WordTrace (prefixWord ++ tailWord_2043266) baseStart_2043266 baseEnd_2043266 := by
    simpa [prefixWord, tailWord_2043266, baseEnd_2043266] using wordTrace_append hprefix tailTrace_2043266
  have hstable : (prefixWord ++ tailWord_2043266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043266).length < 2 ^ (prefixWord ++ tailWord_2043266).sum := by decide
  have hdescent : baseEnd_2043266 < baseStart_2043266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043339 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_2043339 : Nat := 118140960795 + 2043339 * 2 ^ 59
def prefixEnd_2043339 : Nat := 4983230072969 + 3 ^ 40 * 2043339 * 2
def baseEnd_2043339 : Nat := 466317798701104960206827

theorem tailTrace_2043339 : CollatzResearch.WordTrace tailWord_2043339 prefixEnd_2043339 466317798701104960206827 := by
  unfold tailWord_2043339
  simp only [CollatzResearch.WordTrace]
  refine ⟨74526695944339252363029071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49684463962892834908686047 74526695944339252363029071)
  ·
    refine ⟨111790043916508878544543607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74526695944339252363029071 111790043916508878544543607)
    ·
      refine ⟨167685065874763317816815411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111790043916508878544543607 167685065874763317816815411)
      ·
        refine ⟨251527598812144976725223117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167685065874763317816815411 251527598812144976725223117)
        ·
          refine ⟨94322849554554366271958669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251527598812144976725223117 94322849554554366271958669)
          ·
            refine ⟨35371068582957887351984501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94322849554554366271958669 35371068582957887351984501)
            ·
              refine ⟨3316037679652301939248547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35371068582957887351984501 3316037679652301939248547)
              ·
                refine ⟨4974056519478452908872821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316037679652301939248547 4974056519478452908872821)
                ·
                  refine ⟨466317798701104960206827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4974056519478452908872821 466317798701104960206827)
                  ·
                    rfl

theorem cell21_2043339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_2043339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043339 prefixEnd_2043339 := by exact prefixLift 2043339
  have htrace : WordTrace (prefixWord ++ tailWord_2043339) baseStart_2043339 baseEnd_2043339 := by
    simpa [prefixWord, tailWord_2043339, baseEnd_2043339] using wordTrace_append hprefix tailTrace_2043339
  have hstable : (prefixWord ++ tailWord_2043339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043339).length < 2 ^ (prefixWord ++ tailWord_2043339).sum := by decide
  have hdescent : baseEnd_2043339 < baseStart_2043339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043429 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2043429 : Nat := 118140960795 + 2043429 * 2 ^ 59
def prefixEnd_2043429 : Nat := 4983230072969 + 3 ^ 40 * 2043429 * 2
def baseEnd_2043429 : Nat := 466338337927284803706643

theorem tailTrace_2043429 : CollatzResearch.WordTrace tailWord_2043429 prefixEnd_2043429 466338337927284803706643 := by
  unfold tailWord_2043429
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529978514013197733805341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49686652342675465155870227 74529978514013197733805341)
  ·
    refine ⟨27948741942754949150177003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74529978514013197733805341 27948741942754949150177003)
    ·
      refine ⟨41923112914132423725265505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27948741942754949150177003 41923112914132423725265505)
      ·
        refine ⟨31442334685599317793949129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41923112914132423725265505 31442334685599317793949129)
        ·
          refine ⟨23581751014199488345461847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31442334685599317793949129 23581751014199488345461847)
          ·
            refine ⟨35372626521299232518192771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23581751014199488345461847 35372626521299232518192771)
            ·
              refine ⟨53058939781948848777289157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35372626521299232518192771 53058939781948848777289157)
              ·
                refine ⟨9948551209115409145741717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53058939781948848777289157 9948551209115409145741717)
                ·
                  refine ⟨466338337927284803706643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9948551209115409145741717 466338337927284803706643)
                  ·
                    rfl

theorem cell21_2043429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2043429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043429 prefixEnd_2043429 := by exact prefixLift 2043429
  have htrace : WordTrace (prefixWord ++ tailWord_2043429) baseStart_2043429 baseEnd_2043429 := by
    simpa [prefixWord, tailWord_2043429, baseEnd_2043429] using wordTrace_append hprefix tailTrace_2043429
  have hstable : (prefixWord ++ tailWord_2043429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043429).length < 2 ^ (prefixWord ++ tailWord_2043429).sum := by decide
  have hdescent : baseEnd_2043429 < baseStart_2043429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043595 : List Nat := [1, 1, 1, 1, 3, 2, 1, 11]
def baseStart_2043595 : Nat := 118140960795 + 2043595 * 2 ^ 59
def prefixEnd_2043595 : Nat := 4983230072969 + 3 ^ 40 * 2043595 * 2
def baseEnd_2043595 : Nat := 155458740462968467979879

theorem tailTrace_2043595 : CollatzResearch.WordTrace tailWord_2043595 prefixEnd_2043595 155458740462968467979879 := by
  unfold tailWord_2043595
  simp only [CollatzResearch.WordTrace]
  refine ⟨74536033031411808084348239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49690688687607872056232159 74536033031411808084348239)
  ·
    refine ⟨111804049547117712126522359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74536033031411808084348239 111804049547117712126522359)
    ·
      refine ⟨167706074320676568189783539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111804049547117712126522359 167706074320676568189783539)
      ·
        refine ⟨251559111481014852284675309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167706074320676568189783539 251559111481014852284675309)
        ·
          refine ⟨94334666805380569606753241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251559111481014852284675309 94334666805380569606753241)
          ·
            refine ⟨70751000104035427205064931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94334666805380569606753241 70751000104035427205064931)
            ·
              refine ⟨106126500156053140807597397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70751000104035427205064931 106126500156053140807597397)
              ·
                refine ⟨155458740462968467979879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106126500156053140807597397 155458740462968467979879)
                ·
                  rfl

theorem cell21_2043595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_2043595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043595 prefixEnd_2043595 := by exact prefixLift 2043595
  have htrace : WordTrace (prefixWord ++ tailWord_2043595) baseStart_2043595 baseEnd_2043595 := by
    simpa [prefixWord, tailWord_2043595, baseEnd_2043595] using wordTrace_append hprefix tailTrace_2043595
  have hstable : (prefixWord ++ tailWord_2043595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043595).length < 2 ^ (prefixWord ++ tailWord_2043595).sum := by decide
  have hdescent : baseEnd_2043595 < baseStart_2043595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043660 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_2043660 : Nat := 118140960795 + 2043660 * 2 ^ 59
def prefixEnd_2043660 : Nat := 4983230072969 + 3 ^ 40 * 2043660 * 2
def baseEnd_2043660 : Nat := 466391055274479735356171

theorem tailTrace_2043660 : CollatzResearch.WordTrace tailWord_2043660 prefixEnd_2043660 466391055274479735356171 := by
  unfold tailWord_2043660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269201888088162092732217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49692269184117549456976289 37269201888088162092732217)
  ·
    refine ⟨27951901416066121569549163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37269201888088162092732217 27951901416066121569549163)
    ·
      refine ⟨41927852124099182354323745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27951901416066121569549163 41927852124099182354323745)
      ·
        refine ⟨31445889093074386765742809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41927852124099182354323745 31445889093074386765742809)
        ·
          refine ⟨23584416819805790074307107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31445889093074386765742809 23584416819805790074307107)
          ·
            refine ⟨35376625229708685111460661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23584416819805790074307107 35376625229708685111460661)
            ·
              refine ⟨3316558615285189229199437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35376625229708685111460661 3316558615285189229199437)
              ·
                refine ⟨1243709480731945960949789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3316558615285189229199437 1243709480731945960949789)
                ·
                  refine ⟨466391055274479735356171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243709480731945960949789 466391055274479735356171)
                  ·
                    rfl

theorem cell21_2043660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_2043660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043660 prefixEnd_2043660 := by exact prefixLift 2043660
  have htrace : WordTrace (prefixWord ++ tailWord_2043660) baseStart_2043660 baseEnd_2043660 := by
    simpa [prefixWord, tailWord_2043660, baseEnd_2043660] using wordTrace_append hprefix tailTrace_2043660
  have hstable : (prefixWord ++ tailWord_2043660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043660).length < 2 ^ (prefixWord ++ tailWord_2043660).sum := by decide
  have hdescent : baseEnd_2043660 < baseStart_2043660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043688 : List Nat := [2, 1, 5, 1, 1, 2, 1, 8]
def baseStart_2043688 : Nat := 118140960795 + 2043688 * 2 ^ 59
def prefixEnd_2043688 : Nat := 4983230072969 + 3 ^ 40 * 2043688 * 2
def baseEnd_2043688 : Nat := 155465815085319302963149

theorem tailTrace_2043688 : CollatzResearch.WordTrace tailWord_2043688 prefixEnd_2043688 155465815085319302963149 := by
  unfold tailWord_2043688
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269712510037442483741859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49692950013383256644989145 37269712510037442483741859)
  ·
    refine ⟨55904568765056163725612789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37269712510037442483741859 55904568765056163725612789)
    ·
      refine ⟨5241053321724015349276199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55904568765056163725612789 5241053321724015349276199)
      ·
        refine ⟨7861579982586023023914299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241053321724015349276199 7861579982586023023914299)
        ·
          refine ⟨11792369973879034535871449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7861579982586023023914299 11792369973879034535871449)
          ·
            refine ⟨8844277480409275901903587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11792369973879034535871449 8844277480409275901903587)
            ·
              refine ⟨13266416220613913852855381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8844277480409275901903587 13266416220613913852855381)
              ·
                refine ⟨155465815085319302963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13266416220613913852855381 155465815085319302963149)
                ·
                  rfl

theorem cell21_2043688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_2043688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043688 prefixEnd_2043688 := by exact prefixLift 2043688
  have htrace : WordTrace (prefixWord ++ tailWord_2043688) baseStart_2043688 baseEnd_2043688 := by
    simpa [prefixWord, tailWord_2043688, baseEnd_2043688] using wordTrace_append hprefix tailTrace_2043688
  have hstable : (prefixWord ++ tailWord_2043688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043688).length < 2 ^ (prefixWord ++ tailWord_2043688).sum := by decide
  have hdescent : baseEnd_2043688 < baseStart_2043688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043784 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_2043784 : Nat := 118140960795 + 2043784 * 2 ^ 59
def prefixEnd_2043784 : Nat := 4983230072969 + 3 ^ 40 * 2043784 * 2
def baseEnd_2043784 : Nat := 466419353763883075289251

theorem tailTrace_2043784 : CollatzResearch.WordTrace tailWord_2043784 prefixEnd_2043784 466419353763883075289251 := by
  unfold tailWord_2043784
  simp only [CollatzResearch.WordTrace]
  refine ⟨37271463213863546681489203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49695284285151395575318937 37271463213863546681489203)
  ·
    refine ⟨55907194820795320022233805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37271463213863546681489203 55907194820795320022233805)
    ·
      refine ⟨20965198057798245008337677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55907194820795320022233805 20965198057798245008337677)
      ·
        refine ⟨7861949271674341878126629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20965198057798245008337677 7861949271674341878126629)
        ·
          refine ⟨1474115488438939102148743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7861949271674341878126629 1474115488438939102148743)
          ·
            refine ⟨2211173232658408653223115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474115488438939102148743 2211173232658408653223115)
            ·
              refine ⟨3316759848987612979834673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211173232658408653223115 3316759848987612979834673)
              ·
                refine ⟨2487569886740709734876005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316759848987612979834673 2487569886740709734876005)
                ·
                  refine ⟨466419353763883075289251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487569886740709734876005 466419353763883075289251)
                  ·
                    rfl

theorem cell21_2043784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_2043784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043784 prefixEnd_2043784 := by exact prefixLift 2043784
  have htrace : WordTrace (prefixWord ++ tailWord_2043784) baseStart_2043784 baseEnd_2043784 := by
    simpa [prefixWord, tailWord_2043784, baseEnd_2043784] using wordTrace_append hprefix tailTrace_2043784
  have hstable : (prefixWord ++ tailWord_2043784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043784).length < 2 ^ (prefixWord ++ tailWord_2043784).sum := by decide
  have hdescent : baseEnd_2043784 < baseStart_2043784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043823 : List Nat := [1, 1, 2, 1, 2, 2, 5, 7]
def baseStart_2043823 : Nat := 118140960795 + 2043823 * 2 ^ 59
def prefixEnd_2043823 : Nat := 4983230072969 + 3 ^ 40 * 2043823 * 2
def baseEnd_2043823 : Nat := 155476084698409224713057

theorem tailTrace_2043823 : CollatzResearch.WordTrace tailWord_2043823 prefixEnd_2043823 155476084698409224713057 := by
  unfold tailWord_2043823
  simp only [CollatzResearch.WordTrace]
  refine ⟨74544348874585803023648123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49696232583057202015765415 74544348874585803023648123)
  ·
    refine ⟨111816523311878704535472185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74544348874585803023648123 111816523311878704535472185)
    ·
      refine ⟨83862392483909028401604139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111816523311878704535472185 83862392483909028401604139)
      ·
        refine ⟨125793588725863542602406209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83862392483909028401604139 125793588725863542602406209)
        ·
          refine ⟨94345191544397656951804657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125793588725863542602406209 94345191544397656951804657)
          ·
            refine ⟨70758893658298242713853493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94345191544397656951804657 70758893658298242713853493)
            ·
              refine ⟨6633646280465460254423765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70758893658298242713853493 6633646280465460254423765)
              ·
                refine ⟨155476084698409224713057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6633646280465460254423765 155476084698409224713057)
                ·
                  rfl

theorem cell21_2043823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_2043823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043823 prefixEnd_2043823 := by exact prefixLift 2043823
  have htrace : WordTrace (prefixWord ++ tailWord_2043823) baseStart_2043823 baseEnd_2043823 := by
    simpa [prefixWord, tailWord_2043823, baseEnd_2043823] using wordTrace_append hprefix tailTrace_2043823
  have hstable : (prefixWord ++ tailWord_2043823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043823).length < 2 ^ (prefixWord ++ tailWord_2043823).sum := by decide
  have hdescent : baseEnd_2043823 < baseStart_2043823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043829 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 3]
def baseStart_2043829 : Nat := 118140960795 + 2043829 * 2 ^ 59
def prefixEnd_2043829 : Nat := 4983230072969 + 3 ^ 40 * 2043829 * 2
def baseEnd_2043829 : Nat := 466429623376972997039159

theorem tailTrace_2043829 : CollatzResearch.WordTrace tailWord_2043829 prefixEnd_2043829 466429623376972997039159 := by
  unfold tailWord_2043829
  simp only [CollatzResearch.WordTrace]
  refine ⟨74544567712564066048366541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49696378475042710698911027 74544567712564066048366541)
  ·
    refine ⟨27954212892211524768137453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74544567712564066048366541 27954212892211524768137453)
    ·
      refine ⟨10482829834579321788051545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27954212892211524768137453 10482829834579321788051545)
      ·
        refine ⟨7862122375934491341038659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10482829834579321788051545 7862122375934491341038659)
        ·
          refine ⟨11793183563901737011557989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862122375934491341038659 11793183563901737011557989)
          ·
            refine ⟨2211221918231575689667123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11793183563901737011557989 2211221918231575689667123)
            ·
              refine ⟨3316832877347363534500685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211221918231575689667123 3316832877347363534500685)
              ·
                refine ⟨1243812329005261325437757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3316832877347363534500685 1243812329005261325437757)
                ·
                  refine ⟨466429623376972997039159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243812329005261325437757 466429623376972997039159)
                  ·
                    rfl

theorem cell21_2043829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_2043829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043829 prefixEnd_2043829 := by exact prefixLift 2043829
  have htrace : WordTrace (prefixWord ++ tailWord_2043829) baseStart_2043829 baseEnd_2043829 := by
    simpa [prefixWord, tailWord_2043829, baseEnd_2043829] using wordTrace_append hprefix tailTrace_2043829
  have hstable : (prefixWord ++ tailWord_2043829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043829).length < 2 ^ (prefixWord ++ tailWord_2043829).sum := by decide
  have hdescent : baseEnd_2043829 < baseStart_2043829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043930 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2043930 : Nat := 118140960795 + 2043930 * 2 ^ 59
def prefixEnd_2043930 : Nat := 4983230072969 + 3 ^ 40 * 2043930 * 2
def baseEnd_2043930 : Nat := 466452672953019265855619

theorem tailTrace_2043930 : CollatzResearch.WordTrace tailWord_2043930 prefixEnd_2043930 466452672953019265855619 := by
  unfold tailWord_2043930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637062871299540074448311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49698834323465440198528829 18637062871299540074448311)
  ·
    refine ⟨27955594306949310111672467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18637062871299540074448311 27955594306949310111672467)
    ·
      refine ⟨41933391460423965167508701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27955594306949310111672467 41933391460423965167508701)
      ·
        refine ⟨15725021797658986937815763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41933391460423965167508701 15725021797658986937815763)
        ·
          refine ⟨23587532696488480406723645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725021797658986937815763 23587532696488480406723645)
          ·
            refine ⟨8845324761183180152521367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23587532696488480406723645 8845324761183180152521367)
            ·
              refine ⟨13267987141774770228782051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845324761183180152521367 13267987141774770228782051)
              ·
                refine ⟨19901980712662155343173077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267987141774770228782051 19901980712662155343173077)
                ·
                  refine ⟨466452672953019265855619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19901980712662155343173077 466452672953019265855619)
                  ·
                    rfl

theorem cell21_2043930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2043930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043930 prefixEnd_2043930 := by exact prefixLift 2043930
  have htrace : WordTrace (prefixWord ++ tailWord_2043930) baseStart_2043930 baseEnd_2043930 := by
    simpa [prefixWord, tailWord_2043930, baseEnd_2043930] using wordTrace_append hprefix tailTrace_2043930
  have hstable : (prefixWord ++ tailWord_2043930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043930).length < 2 ^ (prefixWord ++ tailWord_2043930).sum := by decide
  have hdescent : baseEnd_2043930 < baseStart_2043930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043933 : List Nat := [1, 4, 2, 2, 2, 2, 3, 5]
def baseStart_2043933 : Nat := 118140960795 + 2043933 * 2 ^ 59
def prefixEnd_2043933 : Nat := 4983230072969 + 3 ^ 40 * 2043933 * 2
def baseEnd_2043933 : Nat := 155484452531297309101871

theorem tailTrace_2043933 : CollatzResearch.WordTrace tailWord_2043933 prefixEnd_2043933 155484452531297309101871 := by
  unfold tailWord_2043933
  simp only [CollatzResearch.WordTrace]
  refine ⟨74548360904187291810152453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49698907269458194540101635 74548360904187291810152453)
  ·
    refine ⟨13977817669535117214403585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74548360904187291810152453 13977817669535117214403585)
    ·
      refine ⟨10483363252151337910802689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13977817669535117214403585 10483363252151337910802689)
      ·
        refine ⟨7862522439113503433102017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10483363252151337910802689 7862522439113503433102017)
        ·
          refine ⟨5896891829335127574826513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7862522439113503433102017 5896891829335127574826513)
          ·
            refine ⟨4422668872001345681119885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896891829335127574826513 4422668872001345681119885)
            ·
              refine ⟨1658500827000504630419957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4422668872001345681119885 1658500827000504630419957)
              ·
                refine ⟨155484452531297309101871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1658500827000504630419957 155484452531297309101871)
                ·
                  rfl

theorem cell21_2043933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 5].length) (baseStart_2043933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043933 prefixEnd_2043933 := by exact prefixLift 2043933
  have htrace : WordTrace (prefixWord ++ tailWord_2043933) baseStart_2043933 baseEnd_2043933 := by
    simpa [prefixWord, tailWord_2043933, baseEnd_2043933] using wordTrace_append hprefix tailTrace_2043933
  have hstable : (prefixWord ++ tailWord_2043933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043933).length < 2 ^ (prefixWord ++ tailWord_2043933).sum := by decide
  have hdescent : baseEnd_2043933 < baseStart_2043933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043975 : List Nat := [1, 1, 4, 1, 3, 1, 2, 8]
def baseStart_2043975 : Nat := 118140960795 + 2043975 * 2 ^ 59
def prefixEnd_2043975 : Nat := 4983230072969 + 3 ^ 40 * 2043975 * 2
def baseEnd_2043975 : Nat := 155487647522036395868509

theorem tailTrace_2043975 : CollatzResearch.WordTrace tailWord_2043975 prefixEnd_2043975 155487647522036395868509 := by
  unfold tailWord_2043975
  simp only [CollatzResearch.WordTrace]
  refine ⟨74549892770035132983181379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49699928513356755322120919 74549892770035132983181379)
  ·
    refine ⟨111824839155052699474772069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74549892770035132983181379 111824839155052699474772069)
    ·
      refine ⟨20967157341572381151519763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111824839155052699474772069 20967157341572381151519763)
      ·
        refine ⟨31450736012358571727279645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20967157341572381151519763 31450736012358571727279645)
        ·
          refine ⟨11794026004634464397729867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31450736012358571727279645 11794026004634464397729867)
          ·
            refine ⟨17691039006951696596594801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11794026004634464397729867 17691039006951696596594801)
            ·
              refine ⟨13268279255213772447446101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17691039006951696596594801 13268279255213772447446101)
              ·
                refine ⟨155487647522036395868509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13268279255213772447446101 155487647522036395868509)
                ·
                  rfl

theorem cell21_2043975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_2043975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043975 prefixEnd_2043975 := by exact prefixLift 2043975
  have htrace : WordTrace (prefixWord ++ tailWord_2043975) baseStart_2043975 baseEnd_2043975 := by
    simpa [prefixWord, tailWord_2043975, baseEnd_2043975] using wordTrace_append hprefix tailTrace_2043975
  have hstable : (prefixWord ++ tailWord_2043975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043975).length < 2 ^ (prefixWord ++ tailWord_2043975).sum := by decide
  have hdescent : baseEnd_2043975 < baseStart_2043975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043992 : List Nat := [2, 1, 2, 2, 1, 4, 4, 5]
def baseStart_2043992 : Nat := 118140960795 + 2043992 * 2 ^ 59
def prefixEnd_2043992 : Nat := 4983230072969 + 3 ^ 40 * 2043992 * 2
def baseEnd_2043992 : Nat := 155488940732573645274053

theorem tailTrace_2043992 : CollatzResearch.WordTrace tailWord_2043992 prefixEnd_2043992 155488940732573645274053 := by
  unfold tailWord_2043992
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275256405486772443275115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49700341873982363257700153 37275256405486772443275115)
  ·
    refine ⟨55912884608230158664912673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37275256405486772443275115 55912884608230158664912673)
    ·
      refine ⟨41934663456172618998684505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55912884608230158664912673 41934663456172618998684505)
      ·
        refine ⟨31450997592129464249013379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41934663456172618998684505 31450997592129464249013379)
        ·
          refine ⟨47176496388194196373520069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31450997592129464249013379 47176496388194196373520069)
          ·
            refine ⟨8845593072786411820035013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47176496388194196373520069 8845593072786411820035013)
            ·
              refine ⟨1658548701147452216256565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8845593072786411820035013 1658548701147452216256565)
              ·
                refine ⟨155488940732573645274053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1658548701147452216256565 155488940732573645274053)
                ·
                  rfl

theorem cell21_2043992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_2043992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2043992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2043992 prefixEnd_2043992 := by exact prefixLift 2043992
  have htrace : WordTrace (prefixWord ++ tailWord_2043992) baseStart_2043992 baseEnd_2043992 := by
    simpa [prefixWord, tailWord_2043992, baseEnd_2043992] using wordTrace_append hprefix tailTrace_2043992
  have hstable : (prefixWord ++ tailWord_2043992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043992).length < 2 ^ (prefixWord ++ tailWord_2043992).sum := by decide
  have hdescent : baseEnd_2043992 < baseStart_2043992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044023 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 5]
def baseStart_2044023 : Nat := 118140960795 + 2044023 * 2 ^ 59
def prefixEnd_2044023 : Nat := 4983230072969 + 3 ^ 40 * 2044023 * 2
def baseEnd_2044023 : Nat := 466473896820071770805429

theorem tailTrace_2044023 : CollatzResearch.WordTrace tailWord_2044023 prefixEnd_2044023 466473896820071770805429 := by
  unfold tailWord_2044023
  simp only [CollatzResearch.WordTrace]
  refine ⟨74551643473861237180928723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49701095649240824787285815 74551643473861237180928723)
  ·
    refine ⟨111827465210791855771393085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74551643473861237180928723 111827465210791855771393085)
    ·
      refine ⟨41935299454046945914272407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111827465210791855771393085 41935299454046945914272407)
      ·
        refine ⟨62902949181070418871408611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41935299454046945914272407 62902949181070418871408611)
        ·
          refine ⟨94354423771605628307112917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62902949181070418871408611 94354423771605628307112917)
          ·
            refine ⟨2211431807147006913447959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 94354423771605628307112917 2211431807147006913447959)
            ·
              refine ⟨3317147710720510370171939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211431807147006913447959 3317147710720510370171939)
              ·
                refine ⟨4975721566080765555257909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317147710720510370171939 4975721566080765555257909)
                ·
                  refine ⟨466473896820071770805429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4975721566080765555257909 466473896820071770805429)
                  ·
                    rfl

theorem cell21_2044023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_2044023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044023 prefixEnd_2044023 := by exact prefixLift 2044023
  have htrace : WordTrace (prefixWord ++ tailWord_2044023) baseStart_2044023 baseEnd_2044023 := by
    simpa [prefixWord, tailWord_2044023, baseEnd_2044023] using wordTrace_append hprefix tailTrace_2044023
  have hstable : (prefixWord ++ tailWord_2044023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044023).length < 2 ^ (prefixWord ++ tailWord_2044023).sum := by decide
  have hdescent : baseEnd_2044023 < baseStart_2044023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044068 : List Nat := [2, 3, 1, 2, 5, 8]
def baseStart_2044068 : Nat := 118140960795 + 2044068 * 2 ^ 59
def prefixEnd_2044068 : Nat := 4983230072969 + 3 ^ 40 * 2044068 * 2
def baseEnd_2044068 : Nat := 17277191349376358983531

theorem tailTrace_2044068 : CollatzResearch.WordTrace tailWord_2044068 prefixEnd_2044068 17277191349376358983531 := by
  unfold tailWord_2044068
  simp only [CollatzResearch.WordTrace]
  refine ⟨37276642379349104933158429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49702189839132139910877905 37276642379349104933158429)
  ·
    refine ⟨13978740892255914349934411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37276642379349104933158429 13978740892255914349934411)
    ·
      refine ⟨20968111338383871524901617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13978740892255914349934411 20968111338383871524901617)
      ·
        refine ⟨15726083503787903643676213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20968111338383871524901617 15726083503787903643676213)
        ·
          refine ⟨1474320328480115966594645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15726083503787903643676213 1474320328480115966594645)
          ·
            refine ⟨17277191349376358983531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1474320328480115966594645 17277191349376358983531)
            ·
              rfl

theorem cell21_2044068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 8].length) (baseStart_2044068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044068 prefixEnd_2044068 := by exact prefixLift 2044068
  have htrace : WordTrace (prefixWord ++ tailWord_2044068) baseStart_2044068 baseEnd_2044068 := by
    simpa [prefixWord, tailWord_2044068, baseEnd_2044068] using wordTrace_append hprefix tailTrace_2044068
  have hstable : (prefixWord ++ tailWord_2044068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044068).length < 2 ^ (prefixWord ++ tailWord_2044068).sum := by decide
  have hdescent : baseEnd_2044068 < baseStart_2044068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044071 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_2044071 : Nat := 118140960795 + 2044071 * 2 ^ 59
def prefixEnd_2044071 : Nat := 4983230072969 + 3 ^ 40 * 2044071 * 2
def baseEnd_2044071 : Nat := 466484851074034354005331

theorem tailTrace_2044071 : CollatzResearch.WordTrace tailWord_2044071 prefixEnd_2044071 466484851074034354005331 := by
  unfold tailWord_2044071
  simp only [CollatzResearch.WordTrace]
  refine ⟨74553394177687341378676067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49702262785124894252450711 74553394177687341378676067)
  ·
    refine ⟨111830091266531012068014101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74553394177687341378676067 111830091266531012068014101)
    ·
      refine ⟨5242035528118641190688161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111830091266531012068014101 5242035528118641190688161)
      ·
        refine ⟨3931526646088980893016121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242035528118641190688161 3931526646088980893016121)
        ·
          refine ⟨2948644984566735669762091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931526646088980893016121 2948644984566735669762091)
          ·
            refine ⟨4422967476850103504643137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948644984566735669762091 4422967476850103504643137)
            ·
              refine ⟨3317225607637577628482353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422967476850103504643137 3317225607637577628482353)
              ·
                refine ⟨2487919205728183221361765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317225607637577628482353 2487919205728183221361765)
                ·
                  refine ⟨466484851074034354005331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2487919205728183221361765 466484851074034354005331)
                  ·
                    rfl

theorem cell21_2044071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_2044071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044071 prefixEnd_2044071 := by exact prefixLift 2044071
  have htrace : WordTrace (prefixWord ++ tailWord_2044071) baseStart_2044071 baseEnd_2044071 := by
    simpa [prefixWord, tailWord_2044071, baseEnd_2044071] using wordTrace_append hprefix tailTrace_2044071
  have hstable : (prefixWord ++ tailWord_2044071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044071).length < 2 ^ (prefixWord ++ tailWord_2044071).sum := by decide
  have hdescent : baseEnd_2044071 < baseStart_2044071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044082 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2044082 : Nat := 118140960795 + 2044082 * 2 ^ 59
def prefixEnd_2044082 : Nat := 4983230072969 + 3 ^ 40 * 2044082 * 2
def baseEnd_2044082 : Nat := 466487361423900779321975

theorem tailTrace_2044082 : CollatzResearch.WordTrace tailWord_2044082 prefixEnd_2044082 466487361423900779321975 := by
  unfold tailWord_2044082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638448845161872564331625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49702530253764993504884333 18638448845161872564331625)
  ·
    refine ⟨13978836633871404423248719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18638448845161872564331625 13978836633871404423248719)
    ·
      refine ⟨20968254950807106634873079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13978836633871404423248719 20968254950807106634873079)
      ·
        refine ⟨31452382426210659952309619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20968254950807106634873079 31452382426210659952309619)
        ·
          refine ⟨47178573639315989928464429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31452382426210659952309619 47178573639315989928464429)
          ·
            refine ⟨17691965114743496223174161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47178573639315989928464429 17691965114743496223174161)
            ·
              refine ⟨13268973836057622167380621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17691965114743496223174161 13268973836057622167380621)
              ·
                refine ⟨4975865188521608312767733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13268973836057622167380621 4975865188521608312767733)
                ·
                  refine ⟨466487361423900779321975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4975865188521608312767733 466487361423900779321975)
                  ·
                    rfl

theorem cell21_2044082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2044082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044082 prefixEnd_2044082 := by exact prefixLift 2044082
  have htrace : WordTrace (prefixWord ++ tailWord_2044082) baseStart_2044082 baseEnd_2044082 := by
    simpa [prefixWord, tailWord_2044082, baseEnd_2044082] using wordTrace_append hprefix tailTrace_2044082
  have hstable : (prefixWord ++ tailWord_2044082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044082).length < 2 ^ (prefixWord ++ tailWord_2044082).sum := by decide
  have hdescent : baseEnd_2044082 < baseStart_2044082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044172 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_2044172 : Nat := 118140960795 + 2044172 * 2 ^ 59
def prefixEnd_2044172 : Nat := 4983230072969 + 3 ^ 40 * 2044172 * 2
def baseEnd_2044172 : Nat := 466507900650080622821791

theorem tailTrace_2044172 : CollatzResearch.WordTrace tailWord_2044172 prefixEnd_2044172 466507900650080622821791 := by
  unfold tailWord_2044172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278538975160717814051385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49704718633547623752068513 37278538975160717814051385)
  ·
    refine ⟨27958904231370538360538539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37278538975160717814051385 27958904231370538360538539)
    ·
      refine ⟨41938356347055807540807809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27958904231370538360538539 41938356347055807540807809)
      ·
        refine ⟨31453767260291855655605857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41938356347055807540807809 31453767260291855655605857)
        ·
          refine ⟨23590325445218891741704393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31453767260291855655605857 23590325445218891741704393)
          ·
            refine ⟨17692744083914168806278295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23590325445218891741704393 17692744083914168806278295)
            ·
              refine ⟨26539116125871253209417443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17692744083914168806278295 26539116125871253209417443)
              ·
                refine ⟨39808674188806879814126165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26539116125871253209417443 39808674188806879814126165)
                ·
                  refine ⟨466507900650080622821791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39808674188806879814126165 466507900650080622821791)
                  ·
                    rfl

theorem cell21_2044172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_2044172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044172 prefixEnd_2044172 := by exact prefixLift 2044172
  have htrace : WordTrace (prefixWord ++ tailWord_2044172) baseStart_2044172 baseEnd_2044172 := by
    simpa [prefixWord, tailWord_2044172, baseEnd_2044172] using wordTrace_append hprefix tailTrace_2044172
  have hstable : (prefixWord ++ tailWord_2044172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044172).length < 2 ^ (prefixWord ++ tailWord_2044172).sum := by decide
  have hdescent : baseEnd_2044172 < baseStart_2044172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044293 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2044293 : Nat := 118140960795 + 2044293 * 2 ^ 59
def prefixEnd_2044293 : Nat := 4983230072969 + 3 ^ 40 * 2044293 * 2
def baseEnd_2044293 : Nat := 466535514498611301304877

theorem tailTrace_2044293 : CollatzResearch.WordTrace tailWord_2044293 prefixEnd_2044293 466535514498611301304877 := by
  unfold tailWord_2044293
  simp only [CollatzResearch.WordTrace]
  refine ⟨74561491182883073293257533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49707660788588715528838355 74561491182883073293257533)
  ·
    refine ⟨27960559193581152484971575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74561491182883073293257533 27960559193581152484971575)
    ·
      refine ⟨41940838790371728727457363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27960559193581152484971575 41940838790371728727457363)
      ·
        refine ⟨62911258185557593091186045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41940838790371728727457363 62911258185557593091186045)
        ·
          refine ⟨23591721819584097409194767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62911258185557593091186045 23591721819584097409194767)
          ·
            refine ⟨35387582729376146113792151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591721819584097409194767 35387582729376146113792151)
            ·
              refine ⟨53081374094064219170688227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35387582729376146113792151 53081374094064219170688227)
              ·
                refine ⟨79622061141096328756032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53081374094064219170688227 79622061141096328756032341)
                ·
                  refine ⟨466535514498611301304877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79622061141096328756032341 466535514498611301304877)
                  ·
                    rfl

theorem cell21_2044293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2044293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044293 prefixEnd_2044293 := by exact prefixLift 2044293
  have htrace : WordTrace (prefixWord ++ tailWord_2044293) baseStart_2044293 baseEnd_2044293 := by
    simpa [prefixWord, tailWord_2044293, baseEnd_2044293] using wordTrace_append hprefix tailTrace_2044293
  have hstable : (prefixWord ++ tailWord_2044293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044293).length < 2 ^ (prefixWord ++ tailWord_2044293).sum := by decide
  have hdescent : baseEnd_2044293 < baseStart_2044293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044330 : List Nat := [3, 1, 6, 1, 1, 1, 1, 7]
def baseStart_2044330 : Nat := 118140960795 + 2044330 * 2 ^ 59
def prefixEnd_2044330 : Nat := 4983230072969 + 3 ^ 40 * 2044330 * 2
def baseEnd_2044330 : Nat := 155514652800902486396045

theorem tailTrace_2044330 : CollatzResearch.WordTrace tailWord_2044330 prefixEnd_2044330 155514652800902486396045 := by
  unfold tailWord_2044330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640710170937257153088611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49708560455832685741569629 18640710170937257153088611)
  ·
    refine ⟨27961065256405885729632917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18640710170937257153088611 27961065256405885729632917)
    ·
      refine ⟨1310674933894025893576543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27961065256405885729632917 1310674933894025893576543)
      ·
        refine ⟨1966012400841038840364815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310674933894025893576543 1966012400841038840364815)
        ·
          refine ⟨2949018601261558260547223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966012400841038840364815 2949018601261558260547223)
          ·
            refine ⟨4423527901892337390820835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949018601261558260547223 4423527901892337390820835)
            ·
              refine ⟨6635291852838506086231253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423527901892337390820835 6635291852838506086231253)
              ·
                refine ⟨155514652800902486396045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6635291852838506086231253 155514652800902486396045)
                ·
                  rfl

theorem cell21_2044330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_2044330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044330 prefixEnd_2044330 := by exact prefixLift 2044330
  have htrace : WordTrace (prefixWord ++ tailWord_2044330) baseStart_2044330 baseEnd_2044330 := by
    simpa [prefixWord, tailWord_2044330, baseEnd_2044330] using wordTrace_append hprefix tailTrace_2044330
  have hstable : (prefixWord ++ tailWord_2044330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044330).length < 2 ^ (prefixWord ++ tailWord_2044330).sum := by decide
  have hdescent : baseEnd_2044330 < baseStart_2044330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044372 : List Nat := [2, 4, 1, 2, 2, 2, 2, 6]
def baseStart_2044372 : Nat := 118140960795 + 2044372 * 2 ^ 59
def prefixEnd_2044372 : Nat := 4983230072969 + 3 ^ 40 * 2044372 * 2
def baseEnd_2044372 : Nat := 155517847791641573162683

theorem tailTrace_2044372 : CollatzResearch.WordTrace tailWord_2044372 prefixEnd_2044372 155517847791641573162683 := by
  unfold tailWord_2044372
  simp only [CollatzResearch.WordTrace]
  refine ⟨37282186274798434892691685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49709581699731246523588913 37282186274798434892691685)
  ·
    refine ⟨6990409926524706542379691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37282186274798434892691685 6990409926524706542379691)
    ·
      refine ⟨10485614889787059813569537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990409926524706542379691 10485614889787059813569537)
      ·
        refine ⟨7864211167340294860177153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10485614889787059813569537 7864211167340294860177153)
        ·
          refine ⟨5898158375505221145132865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7864211167340294860177153 5898158375505221145132865)
          ·
            refine ⟨4423618781628915858849649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898158375505221145132865 4423618781628915858849649)
            ·
              refine ⟨3317714086221686894137237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423618781628915858849649 3317714086221686894137237)
              ·
                refine ⟨155517847791641573162683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3317714086221686894137237 155517847791641573162683)
                ·
                  rfl

theorem cell21_2044372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_2044372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044372 prefixEnd_2044372 := by exact prefixLift 2044372
  have htrace : WordTrace (prefixWord ++ tailWord_2044372) baseStart_2044372 baseEnd_2044372 := by
    simpa [prefixWord, tailWord_2044372, baseEnd_2044372] using wordTrace_append hprefix tailTrace_2044372
  have hstable : (prefixWord ++ tailWord_2044372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044372).length < 2 ^ (prefixWord ++ tailWord_2044372).sum := by decide
  have hdescent : baseEnd_2044372 < baseStart_2044372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044417 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_2044417 : Nat := 118140960795 + 2044417 * 2 ^ 59
def prefixEnd_2044417 : Nat := 4983230072969 + 3 ^ 40 * 2044417 * 2
def baseEnd_2044417 : Nat := 466563812988014641237957

theorem tailTrace_2044417 : CollatzResearch.WordTrace tailWord_2044417 prefixEnd_2044417 466563812988014641237957 := by
  unfold tailWord_2044417
  simp only [CollatzResearch.WordTrace]
  refine ⟨74566013834433842470771505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49710675889622561647181003 74566013834433842470771505)
  ·
    refine ⟨55924510375825381853078629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74566013834433842470771505 55924510375825381853078629)
    ·
      refine ⟨10485845695467259097452243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55924510375825381853078629 10485845695467259097452243)
      ·
        refine ⟨15728768543200888646178365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10485845695467259097452243 15728768543200888646178365)
        ·
          refine ⟨5898288203700333242316887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15728768543200888646178365 5898288203700333242316887)
          ·
            refine ⟨8847432305550499863475331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898288203700333242316887 8847432305550499863475331)
            ·
              refine ⟨13271148458325749795212997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847432305550499863475331 13271148458325749795212997)
              ·
                refine ⟨2488340335936078086602437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13271148458325749795212997 2488340335936078086602437)
                ·
                  refine ⟨466563812988014641237957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488340335936078086602437 466563812988014641237957)
                  ·
                    rfl

theorem cell21_2044417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_2044417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044417 prefixEnd_2044417 := by exact prefixLift 2044417
  have htrace : WordTrace (prefixWord ++ tailWord_2044417) baseStart_2044417 baseEnd_2044417 := by
    simpa [prefixWord, tailWord_2044417, baseEnd_2044417] using wordTrace_append hprefix tailTrace_2044417
  have hstable : (prefixWord ++ tailWord_2044417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044417).length < 2 ^ (prefixWord ++ tailWord_2044417).sum := by decide
  have hdescent : baseEnd_2044417 < baseStart_2044417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044420 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2044420 : Nat := 118140960795 + 2044420 * 2 ^ 59
def prefixEnd_2044420 : Nat := 4983230072969 + 3 ^ 40 * 2044420 * 2
def baseEnd_2044420 : Nat := 466564497628887302687951

theorem tailTrace_2044420 : CollatzResearch.WordTrace tailWord_2044420 prefixEnd_2044420 466564497628887302687951 := by
  unfold tailWord_2044420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37283061626711486991565357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49710748835615315988753809 37283061626711486991565357)
  ·
    refine ⟨13981148110016807621837009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37283061626711486991565357 13981148110016807621837009)
    ·
      refine ⟨10485861082512605716377757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13981148110016807621837009 10485861082512605716377757)
      ·
        refine ⟨3932197905942227143641659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10485861082512605716377757 3932197905942227143641659)
        ·
          refine ⟨5898296858913340715462489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932197905942227143641659 5898296858913340715462489)
          ·
            refine ⟨4423722644185005536596867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898296858913340715462489 4423722644185005536596867)
            ·
              refine ⟨6635583966277508304895301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423722644185005536596867 6635583966277508304895301)
              ·
                refine ⟨1244171993677032807167869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6635583966277508304895301 1244171993677032807167869)
                ·
                  refine ⟨466564497628887302687951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244171993677032807167869 466564497628887302687951)
                  ·
                    rfl

theorem cell21_2044420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2044420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044420 prefixEnd_2044420 := by exact prefixLift 2044420
  have htrace : WordTrace (prefixWord ++ tailWord_2044420) baseStart_2044420 baseEnd_2044420 := by
    simpa [prefixWord, tailWord_2044420, baseEnd_2044420] using wordTrace_append hprefix tailTrace_2044420
  have hstable : (prefixWord ++ tailWord_2044420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044420).length < 2 ^ (prefixWord ++ tailWord_2044420).sum := by decide
  have hdescent : baseEnd_2044420 < baseStart_2044420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044468 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2044468 : Nat := 118140960795 + 2044468 * 2 ^ 59
def prefixEnd_2044468 : Nat := 4983230072969 + 3 ^ 40 * 2044468 * 2
def baseEnd_2044468 : Nat := 466575451882849885887853

theorem tailTrace_2044468 : CollatzResearch.WordTrace tailWord_2044468 prefixEnd_2044468 466575451882849885887853 := by
  unfold tailWord_2044468
  simp only [CollatzResearch.WordTrace]
  refine ⟨37283936978624539090439029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49711915971499385453918705 37283936978624539090439029)
  ·
    refine ⟨3495369091746050539728659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37283936978624539090439029 3495369091746050539728659)
    ·
      refine ⟨5243053637619075809592989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495369091746050539728659 5243053637619075809592989)
      ·
        refine ⟨1966145114107153428597371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5243053637619075809592989 1966145114107153428597371)
        ·
          refine ⟨2949217671160730142896057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966145114107153428597371 2949217671160730142896057)
          ·
            refine ⟨2211913253370547607172043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949217671160730142896057 2211913253370547607172043)
            ·
              refine ⟨3317869880055821410758065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211913253370547607172043 3317869880055821410758065)
              ·
                refine ⟨2488402410041866058068549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317869880055821410758065 2488402410041866058068549)
                ·
                  refine ⟨466575451882849885887853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488402410041866058068549 466575451882849885887853)
                  ·
                    rfl

theorem cell21_2044468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2044468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044468 prefixEnd_2044468 := by exact prefixLift 2044468
  have htrace : WordTrace (prefixWord ++ tailWord_2044468) baseStart_2044468 baseEnd_2044468 := by
    simpa [prefixWord, tailWord_2044468, baseEnd_2044468] using wordTrace_append hprefix tailTrace_2044468
  have hstable : (prefixWord ++ tailWord_2044468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044468).length < 2 ^ (prefixWord ++ tailWord_2044468).sum := by decide
  have hdescent : baseEnd_2044468 < baseStart_2044468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044583 : List Nat := [1, 1, 6, 3, 10]
def baseStart_2044583 : Nat := 118140960795 + 2044583 * 2 ^ 59
def prefixEnd_2044583 : Nat := 4983230072969 + 3 ^ 40 * 2044583 * 2
def baseEnd_2044583 : Nat := 5760514770983151129271

theorem tailTrace_2044583 : CollatzResearch.WordTrace tailWord_2044583 prefixEnd_2044583 5760514770983151129271 := by
  unfold tailWord_2044583
  simp only [CollatzResearch.WordTrace]
  refine ⟨74572068351832452821314403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49714712234554968547542935 74572068351832452821314403)
  ·
    refine ⟨111858102527748679231971605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74572068351832452821314403 111858102527748679231971605)
    ·
      refine ⟨5243348555988219338998669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111858102527748679231971605 5243348555988219338998669)
      ·
        refine ⟨1966255708495582252124501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5243348555988219338998669 1966255708495582252124501)
        ·
          refine ⟨5760514770983151129271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1966255708495582252124501 5760514770983151129271)
          ·
            rfl

theorem cell21_2044583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 10].length) (baseStart_2044583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044583 prefixEnd_2044583 := by exact prefixLift 2044583
  have htrace : WordTrace (prefixWord ++ tailWord_2044583) baseStart_2044583 baseEnd_2044583 := by
    simpa [prefixWord, tailWord_2044583, baseEnd_2044583] using wordTrace_append hprefix tailTrace_2044583
  have hstable : (prefixWord ++ tailWord_2044583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044583).length < 2 ^ (prefixWord ++ tailWord_2044583).sum := by decide
  have hdescent : baseEnd_2044583 < baseStart_2044583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044589 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2044589 : Nat := 118140960795 + 2044589 * 2 ^ 59
def prefixEnd_2044589 : Nat := 4983230072969 + 3 ^ 40 * 2044589 * 2
def baseEnd_2044589 : Nat := 466603065731380564370939

theorem tailTrace_2044589 : CollatzResearch.WordTrace tailWord_2044589 prefixEnd_2044589 466603065731380564370939 := by
  unfold tailWord_2044589
  simp only [CollatzResearch.WordTrace]
  refine ⟨74572287189810715846032821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49714858126540477230688547 74572287189810715846032821)
  ·
    refine ⟨6991151924044754610565577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74572287189810715846032821 6991151924044754610565577)
    ·
      refine ⟨5243363943033565957924183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991151924044754610565577 5243363943033565957924183)
      ·
        refine ⟨7865045914550348936886275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243363943033565957924183 7865045914550348936886275)
        ·
          refine ⟨11797568871825523405329413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865045914550348936886275 11797568871825523405329413)
          ·
            refine ⟨2212044163467285638499265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11797568871825523405329413 2212044163467285638499265)
            ·
              refine ⟨1659033122600464228874449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212044163467285638499265 1659033122600464228874449)
              ·
                refine ⟨1244274841950348171655837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659033122600464228874449 1244274841950348171655837)
                ·
                  refine ⟨466603065731380564370939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244274841950348171655837 466603065731380564370939)
                  ·
                    rfl

theorem cell21_2044589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2044589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044589 prefixEnd_2044589 := by exact prefixLift 2044589
  have htrace : WordTrace (prefixWord ++ tailWord_2044589) baseStart_2044589 baseEnd_2044589 := by
    simpa [prefixWord, tailWord_2044589, baseEnd_2044589] using wordTrace_append hprefix tailTrace_2044589
  have hstable : (prefixWord ++ tailWord_2044589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044589).length < 2 ^ (prefixWord ++ tailWord_2044589).sum := by decide
  have hdescent : baseEnd_2044589 < baseStart_2044589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044631 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 3]
def baseStart_2044631 : Nat := 118140960795 + 2044631 * 2 ^ 59
def prefixEnd_2044631 : Nat := 4983230072969 + 3 ^ 40 * 2044631 * 2
def baseEnd_2044631 : Nat := 466612650703597824670853

theorem tailTrace_2044631 : CollatzResearch.WordTrace tailWord_2044631 prefixEnd_2044631 466612650703597824670853 := by
  unfold tailWord_2044631
  simp only [CollatzResearch.WordTrace]
  refine ⟨74573819055658557019061747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49715879370439038012707831 74573819055658557019061747)
  ·
    refine ⟨111860728583487835528592621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74573819055658557019061747 111860728583487835528592621)
    ·
      refine ⟨41947773218807938323222233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111860728583487835528592621 41947773218807938323222233)
      ·
        refine ⟨31460829914105953742416675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41947773218807938323222233 31460829914105953742416675)
        ·
          refine ⟨47191244871158930613625013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31460829914105953742416675 47191244871158930613625013)
          ·
            refine ⟨4424179206671149745027345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47191244871158930613625013 4424179206671149745027345)
            ·
              refine ⟨3318134405003362308770509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424179206671149745027345 3318134405003362308770509)
              ·
                refine ⟨1244300401876260865788941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3318134405003362308770509 1244300401876260865788941)
                ·
                  refine ⟨466612650703597824670853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244300401876260865788941 466612650703597824670853)
                  ·
                    rfl

theorem cell21_2044631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3].length) (baseStart_2044631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044631 prefixEnd_2044631 := by exact prefixLift 2044631
  have htrace : WordTrace (prefixWord ++ tailWord_2044631) baseStart_2044631 baseEnd_2044631 := by
    simpa [prefixWord, tailWord_2044631, baseEnd_2044631] using wordTrace_append hprefix tailTrace_2044631
  have hstable : (prefixWord ++ tailWord_2044631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044631).length < 2 ^ (prefixWord ++ tailWord_2044631).sum := by decide
  have hdescent : baseEnd_2044631 < baseStart_2044631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044645 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_2044645 : Nat := 118140960795 + 2044645 * 2 ^ 59
def prefixEnd_2044645 : Nat := 4983230072969 + 3 ^ 40 * 2044645 * 2
def baseEnd_2044645 : Nat := 466615845694336911437491

theorem tailTrace_2044645 : CollatzResearch.WordTrace tailWord_2044645 prefixEnd_2044645 466615845694336911437491 := by
  unfold tailWord_2044645
  simp only [CollatzResearch.WordTrace]
  refine ⟨74574329677607837410071389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49716219785071891606714259 74574329677607837410071389)
  ·
    refine ⟨27965373629102939028776771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74574329677607837410071389 27965373629102939028776771)
    ·
      refine ⟨41948060443654408543165157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27965373629102939028776771 41948060443654408543165157)
      ·
        refine ⟨7865261333185201601843467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41948060443654408543165157 7865261333185201601843467)
        ·
          refine ⟨11797891999777802402765201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865261333185201601843467 11797891999777802402765201)
          ·
            refine ⟨8848418999833351802073901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797891999777802402765201 8848418999833351802073901)
            ·
              refine ⟨3318157124937506925777713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8848418999833351802073901 3318157124937506925777713)
              ·
                refine ⟨2488617843703130194333285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318157124937506925777713 2488617843703130194333285)
                ·
                  refine ⟨466615845694336911437491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488617843703130194333285 466615845694336911437491)
                  ·
                    rfl

theorem cell21_2044645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_2044645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044645 prefixEnd_2044645 := by exact prefixLift 2044645
  have htrace : WordTrace (prefixWord ++ tailWord_2044645) baseStart_2044645 baseEnd_2044645 := by
    simpa [prefixWord, tailWord_2044645, baseEnd_2044645] using wordTrace_append hprefix tailTrace_2044645
  have hstable : (prefixWord ++ tailWord_2044645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044645).length < 2 ^ (prefixWord ++ tailWord_2044645).sum := by decide
  have hdescent : baseEnd_2044645 < baseStart_2044645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044662 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2044662 : Nat := 118140960795 + 2044662 * 2 ^ 59
def prefixEnd_2044662 : Nat := 4983230072969 + 3 ^ 40 * 2044662 * 2
def baseEnd_2044662 : Nat := 466619725325948659654123

theorem tailTrace_2044662 : CollatzResearch.WordTrace tailWord_2044662 prefixEnd_2044662 466619725325948659654123 := by
  unfold tailWord_2044662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660934357409140582090015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49716633145697499542293493 4660934357409140582090015)
  ·
    refine ⟨6991401536113710873135023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660934357409140582090015 6991401536113710873135023)
    ·
      refine ⟨10487102304170566309702535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6991401536113710873135023 10487102304170566309702535)
      ·
        refine ⟨15730653456255849464553803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10487102304170566309702535 15730653456255849464553803)
        ·
          refine ⟨23595980184383774196830705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730653456255849464553803 23595980184383774196830705)
          ·
            refine ⟨17696985138287830647623029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23595980184383774196830705 17696985138287830647623029)
            ·
              refine ⟨1659092356714484123214659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17696985138287830647623029 1659092356714484123214659)
              ·
                refine ⟨2488638535071726184821989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659092356714484123214659 2488638535071726184821989)
                ·
                  refine ⟨466619725325948659654123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488638535071726184821989 466619725325948659654123)
                  ·
                    rfl

theorem cell21_2044662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2044662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044662 prefixEnd_2044662 := by exact prefixLift 2044662
  have htrace : WordTrace (prefixWord ++ tailWord_2044662) baseStart_2044662 baseEnd_2044662 := by
    simpa [prefixWord, tailWord_2044662, baseEnd_2044662] using wordTrace_append hprefix tailTrace_2044662
  have hstable : (prefixWord ++ tailWord_2044662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044662).length < 2 ^ (prefixWord ++ tailWord_2044662).sum := by decide
  have hdescent : baseEnd_2044662 < baseStart_2044662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044687 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_2044687 : Nat := 118140960795 + 2044687 * 2 ^ 59
def prefixEnd_2044687 : Nat := 4983230072969 + 3 ^ 40 * 2044687 * 2
def baseEnd_2044687 : Nat := 466625430666554171737405

theorem tailTrace_2044687 : CollatzResearch.WordTrace tailWord_2044687 prefixEnd_2044687 466625430666554171737405 := by
  unfold tailWord_2044687
  simp only [CollatzResearch.WordTrace]
  refine ⟨74575861543455678583100315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49717241028970452388733543 74575861543455678583100315)
  ·
    refine ⟨111863792315183517874650473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74575861543455678583100315 111863792315183517874650473)
    ·
      refine ⟨83897844236387638405987855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111863792315183517874650473 83897844236387638405987855)
      ·
        refine ⟨125846766354581457608981783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83897844236387638405987855 125846766354581457608981783)
        ·
          refine ⟨188770149531872186413472675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125846766354581457608981783 188770149531872186413472675)
          ·
            refine ⟨283155224297808279620209013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188770149531872186413472675 283155224297808279620209013)
            ·
              refine ⟨26545802277919526214394595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283155224297808279620209013 26545802277919526214394595)
              ·
                refine ⟨39818703416879289321591893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26545802277919526214394595 39818703416879289321591893)
                ·
                  refine ⟨466625430666554171737405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39818703416879289321591893 466625430666554171737405)
                  ·
                    rfl

theorem cell21_2044687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_2044687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044687 prefixEnd_2044687 := by exact prefixLift 2044687
  have htrace : WordTrace (prefixWord ++ tailWord_2044687) baseStart_2044687 baseEnd_2044687 := by
    simpa [prefixWord, tailWord_2044687, baseEnd_2044687] using wordTrace_append hprefix tailTrace_2044687
  have hstable : (prefixWord ++ tailWord_2044687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044687).length < 2 ^ (prefixWord ++ tailWord_2044687).sum := by decide
  have hdescent : baseEnd_2044687 < baseStart_2044687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044704 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_2044704 : Nat := 118140960795 + 2044704 * 2 ^ 59
def prefixEnd_2044704 : Nat := 4983230072969 + 3 ^ 40 * 2044704 * 2
def baseEnd_2044704 : Nat := 466629310298165919954037

theorem tailTrace_2044704 : CollatzResearch.WordTrace tailWord_2044704 prefixEnd_2044704 466629310298165919954037 := by
  unfold tailWord_2044704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37288240792197045243234583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49717654389596060324312777 37288240792197045243234583)
  ·
    refine ⟨55932361188295567864851875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37288240792197045243234583 55932361188295567864851875)
    ·
      refine ⟨83898541782443351797277813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55932361188295567864851875 83898541782443351797277813)
      ·
        refine ⟨7865488292104064230994795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83898541782443351797277813 7865488292104064230994795)
        ·
          refine ⟨11798232438156096346492193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7865488292104064230994795 11798232438156096346492193)
          ·
            refine ⟨8848674328617072259869145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11798232438156096346492193 8848674328617072259869145)
            ·
              refine ⟨6636505746462804194901859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8848674328617072259869145 6636505746462804194901859)
              ·
                refine ⟨9954758619694206292352789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636505746462804194901859 9954758619694206292352789)
                ·
                  refine ⟨466629310298165919954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9954758619694206292352789 466629310298165919954037)
                  ·
                    rfl

theorem cell21_2044704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_2044704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044704 prefixEnd_2044704 := by exact prefixLift 2044704
  have htrace : WordTrace (prefixWord ++ tailWord_2044704) baseStart_2044704 baseEnd_2044704 := by
    simpa [prefixWord, tailWord_2044704, baseEnd_2044704] using wordTrace_append hprefix tailTrace_2044704
  have hstable : (prefixWord ++ tailWord_2044704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044704).length < 2 ^ (prefixWord ++ tailWord_2044704).sum := by decide
  have hdescent : baseEnd_2044704 < baseStart_2044704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044780 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_2044780 : Nat := 118140960795 + 2044780 * 2 ^ 59
def prefixEnd_2044780 : Nat := 4983230072969 + 3 ^ 40 * 2044780 * 2
def baseEnd_2044780 : Nat := 466646654533606676687215

theorem tailTrace_2044780 : CollatzResearch.WordTrace tailWord_2044780 prefixEnd_2044780 466646654533606676687215 := by
  unfold tailWord_2044780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37289626766059377733117897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49719502354745836977490529 37289626766059377733117897)
  ·
    refine ⟨27967220074544533299838423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37289626766059377733117897 27967220074544533299838423)
    ·
      refine ⟨41950830111816799949757635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27967220074544533299838423 41950830111816799949757635)
      ·
        refine ⟨62926245167725199924636453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41950830111816799949757635 62926245167725199924636453)
        ·
          refine ⟨11798670968948474985869335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62926245167725199924636453 11798670968948474985869335)
          ·
            refine ⟨17698006453422712478804003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798670968948474985869335 17698006453422712478804003)
            ·
              refine ⟨26547009680134068718206005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17698006453422712478804003 26547009680134068718206005)
              ·
                refine ⟨2488782157512568942331813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26547009680134068718206005 2488782157512568942331813)
                ·
                  refine ⟨466646654533606676687215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488782157512568942331813 466646654533606676687215)
                  ·
                    rfl

theorem cell21_2044780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_2044780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044780 prefixEnd_2044780 := by exact prefixLift 2044780
  have htrace : WordTrace (prefixWord ++ tailWord_2044780) baseStart_2044780 baseEnd_2044780 := by
    simpa [prefixWord, tailWord_2044780, baseEnd_2044780] using wordTrace_append hprefix tailTrace_2044780
  have hstable : (prefixWord ++ tailWord_2044780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044780).length < 2 ^ (prefixWord ++ tailWord_2044780).sum := by decide
  have hdescent : baseEnd_2044780 < baseStart_2044780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044890 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2044890 : Nat := 118140960795 + 2044890 * 2 ^ 59
def prefixEnd_2044890 : Nat := 4983230072969 + 3 ^ 40 * 2044890 * 2
def baseEnd_2044890 : Nat := 466671758032270929853657

theorem tailTrace_2044890 : CollatzResearch.WordTrace tailWord_2044890 prefixEnd_2044890 466671758032270929853657 := by
  unfold tailWord_2044890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18645816390430061063185031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49722177041146829501826749 18645816390430061063185031)
  ·
    refine ⟨27968724585645091594777547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18645816390430061063185031 27968724585645091594777547)
    ·
      refine ⟨41953086878467637392166321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27968724585645091594777547 41953086878467637392166321)
      ·
        refine ⟨31464815158850728044124741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41953086878467637392166321 31464815158850728044124741)
        ·
          refine ⟨5899652842284511508273389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31464815158850728044124741 5899652842284511508273389)
          ·
            refine ⟨2212369815856691815602521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5899652842284511508273389 2212369815856691815602521)
            ·
              refine ⟨1659277361892518861701891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212369815856691815602521 1659277361892518861701891)
              ·
                refine ⟨2488916042838778292552837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659277361892518861701891 2488916042838778292552837)
                ·
                  refine ⟨466671758032270929853657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488916042838778292552837 466671758032270929853657)
                  ·
                    rfl

theorem cell21_2044890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2044890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044890 prefixEnd_2044890 := by exact prefixLift 2044890
  have htrace : WordTrace (prefixWord ++ tailWord_2044890) baseStart_2044890 baseEnd_2044890 := by
    simpa [prefixWord, tailWord_2044890, baseEnd_2044890] using wordTrace_append hprefix tailTrace_2044890
  have hstable : (prefixWord ++ tailWord_2044890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044890).length < 2 ^ (prefixWord ++ tailWord_2044890).sum := by decide
  have hdescent : baseEnd_2044890 < baseStart_2044890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044963 : List Nat := [1, 1, 1, 4, 3, 3, 3, 5]
def baseStart_2044963 : Nat := 118140960795 + 2044963 * 2 ^ 59
def prefixEnd_2044963 : Nat := 4983230072969 + 3 ^ 40 * 2044963 * 2
def baseEnd_2044963 : Nat := 155562805875613008378947

theorem tailTrace_2044963 : CollatzResearch.WordTrace tailWord_2044963 prefixEnd_2044963 155562805875613008378947 := by
  unfold tailWord_2044963
  simp only [CollatzResearch.WordTrace]
  refine ⟨74585928090455777720147543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49723952060303851813431695 74585928090455777720147543)
  ·
    refine ⟨111878892135683666580221315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74585928090455777720147543 111878892135683666580221315)
    ·
      refine ⟨167818338203525499870331973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111878892135683666580221315 167818338203525499870331973)
      ·
        refine ⟨31465938413161031225687245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167818338203525499870331973 31465938413161031225687245)
        ·
          refine ⟨11799726904935386709632717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31465938413161031225687245 11799726904935386709632717)
          ·
            refine ⟨4424897589350770016112269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11799726904935386709632717 4424897589350770016112269)
            ·
              refine ⟨1659336596006538756042101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4424897589350770016112269 1659336596006538756042101)
              ·
                refine ⟨155562805875613008378947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659336596006538756042101 155562805875613008378947)
                ·
                  rfl

theorem cell21_2044963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 5].length) (baseStart_2044963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2044963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2044963 prefixEnd_2044963 := by exact prefixLift 2044963
  have htrace : WordTrace (prefixWord ++ tailWord_2044963) baseStart_2044963 baseEnd_2044963 := by
    simpa [prefixWord, tailWord_2044963, baseEnd_2044963] using wordTrace_append hprefix tailTrace_2044963
  have hstable : (prefixWord ++ tailWord_2044963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044963).length < 2 ^ (prefixWord ++ tailWord_2044963).sum := by decide
  have hdescent : baseEnd_2044963 < baseStart_2044963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045014 : List Nat := [5, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2045014 : Nat := 118140960795 + 2045014 * 2 ^ 59
def prefixEnd_2045014 : Nat := 4983230072969 + 3 ^ 40 * 2045014 * 2
def baseEnd_2045014 : Nat := 155566685507224756595579

theorem tailTrace_2045014 : CollatzResearch.WordTrace tailWord_2045014 prefixEnd_2045014 155566685507224756595579 := by
  unfold tailWord_2045014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661736763329438339390881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49725192142180675620169397 4661736763329438339390881)
  ·
    refine ⟨3496302572497078754543161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4661736763329438339390881 3496302572497078754543161)
    ·
      refine ⟨2622226929372809065907371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3496302572497078754543161 2622226929372809065907371)
      ·
        refine ⟨3933340394059213598861057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622226929372809065907371 3933340394059213598861057)
        ·
          refine ⟨2950005295544410199145793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933340394059213598861057 2950005295544410199145793)
          ·
            refine ⟨2212503971658307649359345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950005295544410199145793 2212503971658307649359345)
            ·
              refine ⟨1659377978743730737019509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212503971658307649359345 1659377978743730737019509)
              ·
                refine ⟨155566685507224756595579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659377978743730737019509 155566685507224756595579)
                ·
                  rfl

theorem cell21_2045014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2045014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045014 prefixEnd_2045014 := by exact prefixLift 2045014
  have htrace : WordTrace (prefixWord ++ tailWord_2045014) baseStart_2045014 baseEnd_2045014 := by
    simpa [prefixWord, tailWord_2045014, baseEnd_2045014] using wordTrace_append hprefix tailTrace_2045014
  have hstable : (prefixWord ++ tailWord_2045014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045014).length < 2 ^ (prefixWord ++ tailWord_2045014).sum := by decide
  have hdescent : baseEnd_2045014 < baseStart_2045014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045045 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 3]
def baseStart_2045045 : Nat := 118140960795 + 2045045 * 2 ^ 59
def prefixEnd_2045045 : Nat := 4983230072969 + 3 ^ 40 * 2045045 * 2
def baseEnd_2045045 : Nat := 466707131144025104770007

theorem tailTrace_2045045 : CollatzResearch.WordTrace tailWord_2045045 prefixEnd_2045045 466707131144025104770007 := by
  unfold tailWord_2045045
  simp only [CollatzResearch.WordTrace]
  refine ⟨74588918876158705724632589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49725945917439137149755059 74588918876158705724632589)
  ·
    refine ⟨27970844578559514646737221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74588918876158705724632589 27970844578559514646737221)
    ·
      refine ⟨5244533358479908996263229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27970844578559514646737221 5244533358479908996263229)
      ·
        refine ⟨1966700009429965873598711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5244533358479908996263229 1966700009429965873598711)
        ·
          refine ⟨2950050014144948810398067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966700009429965873598711 2950050014144948810398067)
          ·
            refine ⟨4425075021217423215597101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950050014144948810398067 4425075021217423215597101)
            ·
              refine ⟨1659403132956533705848913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4425075021217423215597101 1659403132956533705848913)
              ·
                refine ⟨1244552349717400279386685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659403132956533705848913 1244552349717400279386685)
                ·
                  refine ⟨466707131144025104770007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244552349717400279386685 466707131144025104770007)
                  ·
                    rfl

theorem cell21_2045045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_2045045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045045 prefixEnd_2045045 := by exact prefixLift 2045045
  have htrace : WordTrace (prefixWord ++ tailWord_2045045) baseStart_2045045 baseEnd_2045045 := by
    simpa [prefixWord, tailWord_2045045, baseEnd_2045045] using wordTrace_append hprefix tailTrace_2045045
  have hstable : (prefixWord ++ tailWord_2045045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045045).length < 2 ^ (prefixWord ++ tailWord_2045045).sum := by decide
  have hdescent : baseEnd_2045045 < baseStart_2045045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045174 : List Nat := [5, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2045174 : Nat := 118140960795 + 2045174 * 2 ^ 59
def prefixEnd_2045174 : Nat := 4983230072969 + 3 ^ 40 * 2045174 * 2
def baseEnd_2045174 : Nat := 155578856900516515706581

theorem tailTrace_2045174 : CollatzResearch.WordTrace tailWord_2045174 prefixEnd_2045174 155578856900516515706581 := by
  unfold tailWord_2045174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662101493293210047254911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49729082595127573837385717 4662101493293210047254911)
  ·
    refine ⟨6993152239939815070882367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662101493293210047254911 6993152239939815070882367)
    ·
      refine ⟨10489728359909722606323551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993152239939815070882367 10489728359909722606323551)
      ·
        refine ⟨15734592539864583909485327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10489728359909722606323551 15734592539864583909485327)
        ·
          refine ⟨23601888809796875864227991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15734592539864583909485327 23601888809796875864227991)
          ·
            refine ⟨35402833214695313796341987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23601888809796875864227991 35402833214695313796341987)
            ·
              refine ⟨53104249822042970694512981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35402833214695313796341987 53104249822042970694512981)
              ·
                refine ⟨155578856900516515706581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53104249822042970694512981 155578856900516515706581)
                ·
                  rfl

theorem cell21_2045174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2045174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045174 prefixEnd_2045174 := by exact prefixLift 2045174
  have htrace : WordTrace (prefixWord ++ tailWord_2045174) baseStart_2045174 baseEnd_2045174 := by
    simpa [prefixWord, tailWord_2045174, baseEnd_2045174] using wordTrace_append hprefix tailTrace_2045174
  have hstable : (prefixWord ++ tailWord_2045174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045174).length < 2 ^ (prefixWord ++ tailWord_2045174).sum := by decide
  have hdescent : baseEnd_2045174 < baseStart_2045174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045219 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_2045219 : Nat := 118140960795 + 2045219 * 2 ^ 59
def prefixEnd_2045219 : Nat := 4983230072969 + 3 ^ 40 * 2045219 * 2
def baseEnd_2045219 : Nat := 466746840314639468869651

theorem tailTrace_2045219 : CollatzResearch.WordTrace tailWord_2045219 prefixEnd_2045219 466746840314639468869651 := by
  unfold tailWord_2045219
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595265177528333441466711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49730176785018888960977807 74595265177528333441466711)
  ·
    refine ⟨111892897766292500162200067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74595265177528333441466711 111892897766292500162200067)
    ·
      refine ⟨167839346649438750243300101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111892897766292500162200067 167839346649438750243300101)
      ·
        refine ⟨31469877496769765670618769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167839346649438750243300101 31469877496769765670618769)
        ·
          refine ⟨23602408122577324252964077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31469877496769765670618769 23602408122577324252964077)
          ·
            refine ⟨8850903045966496594861529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23602408122577324252964077 8850903045966496594861529)
            ·
              refine ⟨6638177284474872446146147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8850903045966496594861529 6638177284474872446146147)
              ·
                refine ⟨9957265926712308669219221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638177284474872446146147 9957265926712308669219221)
                ·
                  refine ⟨466746840314639468869651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9957265926712308669219221 466746840314639468869651)
                  ·
                    rfl

theorem cell21_2045219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_2045219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045219 prefixEnd_2045219 := by exact prefixLift 2045219
  have htrace : WordTrace (prefixWord ++ tailWord_2045219) baseStart_2045219 baseEnd_2045219 := by
    simpa [prefixWord, tailWord_2045219, baseEnd_2045219] using wordTrace_append hprefix tailTrace_2045219
  have hstable : (prefixWord ++ tailWord_2045219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045219).length < 2 ^ (prefixWord ++ tailWord_2045219).sum := by decide
  have hdescent : baseEnd_2045219 < baseStart_2045219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045295 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_2045295 : Nat := 118140960795 + 2045295 * 2 ^ 59
def prefixEnd_2045295 : Nat := 4983230072969 + 3 ^ 40 * 2045295 * 2
def baseEnd_2045295 : Nat := 466764184550080225602829

theorem tailTrace_2045295 : CollatzResearch.WordTrace tailWord_2045295 prefixEnd_2045295 466764184550080225602829 := by
  unfold tailWord_2045295
  simp only [CollatzResearch.WordTrace]
  refine ⟨74598037125252998421233339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49732024750168665614155559 74598037125252998421233339)
  ·
    refine ⟨111897055687879497631850009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74598037125252998421233339 111897055687879497631850009)
    ·
      refine ⟨83922791765909623223887507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111897055687879497631850009 83922791765909623223887507)
      ·
        refine ⟨125884187648864434835831261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83922791765909623223887507 125884187648864434835831261)
        ·
          refine ⟨47206570368324163063436723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125884187648864434835831261 47206570368324163063436723)
          ·
            refine ⟨70809855552486244595155085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47206570368324163063436723 70809855552486244595155085)
            ·
              refine ⟨26553695832182341723183157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70809855552486244595155085 26553695832182341723183157)
              ·
                refine ⟨2489408984267094536548421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26553695832182341723183157 2489408984267094536548421)
                ·
                  refine ⟨466764184550080225602829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489408984267094536548421 466764184550080225602829)
                  ·
                    rfl

theorem cell21_2045295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_2045295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045295 prefixEnd_2045295 := by exact prefixLift 2045295
  have htrace : WordTrace (prefixWord ++ tailWord_2045295) baseStart_2045295 baseEnd_2045295 := by
    simpa [prefixWord, tailWord_2045295, baseEnd_2045295] using wordTrace_append hprefix tailTrace_2045295
  have hstable : (prefixWord ++ tailWord_2045295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045295).length < 2 ^ (prefixWord ++ tailWord_2045295).sum := by decide
  have hdescent : baseEnd_2045295 < baseStart_2045295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045402 : List Nat := [3, 1, 1, 2, 3, 3, 2, 6]
def baseStart_2045402 : Nat := 118140960795 + 2045402 * 2 ^ 59
def prefixEnd_2045402 : Nat := 4983230072969 + 3 ^ 40 * 2045402 * 2
def baseEnd_2045402 : Nat := 155596201135957272439759

theorem tailTrace_2045402 : CollatzResearch.WordTrace tailWord_2045402 prefixEnd_2045402 155596201135957272439759 := by
  unfold tailWord_2045402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18650484933966338923844615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49734626490576903796918973 18650484933966338923844615)
  ·
    refine ⟨27975727400949508385766923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18650484933966338923844615 27975727400949508385766923)
    ·
      refine ⟨41963591101424262578650385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27975727400949508385766923 41963591101424262578650385)
      ·
        refine ⟨31472693326068196933987789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41963591101424262578650385 31472693326068196933987789)
        ·
          refine ⟨11802259997275573850245421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31472693326068196933987789 11802259997275573850245421)
          ·
            refine ⟨4425847498978340193842033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11802259997275573850245421 4425847498978340193842033)
            ·
              refine ⟨3319385624233755145381525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425847498978340193842033 3319385624233755145381525)
              ·
                refine ⟨155596201135957272439759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3319385624233755145381525 155596201135957272439759)
                ·
                  rfl

theorem cell21_2045402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_2045402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045402 prefixEnd_2045402 := by exact prefixLift 2045402
  have htrace : WordTrace (prefixWord ++ tailWord_2045402) baseStart_2045402 baseEnd_2045402 := by
    simpa [prefixWord, tailWord_2045402, baseEnd_2045402] using wordTrace_append hprefix tailTrace_2045402
  have hstable : (prefixWord ++ tailWord_2045402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045402).length < 2 ^ (prefixWord ++ tailWord_2045402).sum := by decide
  have hdescent : baseEnd_2045402 < baseStart_2045402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045405 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 4]
def baseStart_2045405 : Nat := 118140960795 + 2045405 * 2 ^ 59
def prefixEnd_2045405 : Nat := 4983230072969 + 3 ^ 40 * 2045405 * 2
def baseEnd_2045405 : Nat := 466789288048744478769271

theorem tailTrace_2045405 : CollatzResearch.WordTrace tailWord_2045405 prefixEnd_2045405 466789288048744478769271 := by
  unfold tailWord_2045405
  simp only [CollatzResearch.WordTrace]
  refine ⟨74602049154854487207737669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49734699436569658138491779 74602049154854487207737669)
  ·
    refine ⟨13987884216535216351450813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74602049154854487207737669 13987884216535216351450813)
    ·
      refine ⟨5245456581200706131794055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13987884216535216351450813 5245456581200706131794055)
      ·
        refine ⟨7868184871801059197691083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245456581200706131794055 7868184871801059197691083)
        ·
          refine ⟨11802277307701588796536625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868184871801059197691083 11802277307701588796536625)
          ·
            refine ⟨8851707980776191597402469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11802277307701588796536625 8851707980776191597402469)
            ·
              refine ⟨1659695246395535924512963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8851707980776191597402469 1659695246395535924512963)
              ·
                refine ⟨2489542869593303886769445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659695246395535924512963 2489542869593303886769445)
                ·
                  refine ⟨466789288048744478769271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489542869593303886769445 466789288048744478769271)
                  ·
                    rfl

theorem cell21_2045405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_2045405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045405 prefixEnd_2045405 := by exact prefixLift 2045405
  have htrace : WordTrace (prefixWord ++ tailWord_2045405) baseStart_2045405 baseEnd_2045405 := by
    simpa [prefixWord, tailWord_2045405, baseEnd_2045405] using wordTrace_append hprefix tailTrace_2045405
  have hstable : (prefixWord ++ tailWord_2045405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045405).length < 2 ^ (prefixWord ++ tailWord_2045405).sum := by decide
  have hdescent : baseEnd_2045405 < baseStart_2045405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045416 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_2045416 : Nat := 118140960795 + 2045416 * 2 ^ 59
def prefixEnd_2045416 : Nat := 4983230072969 + 3 ^ 40 * 2045416 * 2
def baseEnd_2045416 : Nat := 466791798398610904085915

theorem tailTrace_2045416 : CollatzResearch.WordTrace tailWord_2045416 prefixEnd_2045416 466791798398610904085915 := by
  unfold tailWord_2045416
  simp only [CollatzResearch.WordTrace]
  refine ⟨37301225178907318043194051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49734966905209757390925401 37301225178907318043194051)
  ·
    refine ⟨55951837768360977064791077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37301225178907318043194051 55951837768360977064791077)
    ·
      refine ⟨10490969581567683199648327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55951837768360977064791077 10490969581567683199648327)
      ·
        refine ⟨15736454372351524799472491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10490969581567683199648327 15736454372351524799472491)
        ·
          refine ⟨23604681558527287199208737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15736454372351524799472491 23604681558527287199208737)
          ·
            refine ⟨17703511168895465399406553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23604681558527287199208737 17703511168895465399406553)
            ·
              refine ⟨13277633376671599049554915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17703511168895465399406553 13277633376671599049554915)
              ·
                refine ⟨19916450065007398574332373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13277633376671599049554915 19916450065007398574332373)
                ·
                  refine ⟨466791798398610904085915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19916450065007398574332373 466791798398610904085915)
                  ·
                    rfl

theorem cell21_2045416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_2045416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045416 prefixEnd_2045416 := by exact prefixLift 2045416
  have htrace : WordTrace (prefixWord ++ tailWord_2045416) baseStart_2045416 baseEnd_2045416 := by
    simpa [prefixWord, tailWord_2045416, baseEnd_2045416] using wordTrace_append hprefix tailTrace_2045416
  have hstable : (prefixWord ++ tailWord_2045416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045416).length < 2 ^ (prefixWord ++ tailWord_2045416).sum := by decide
  have hdescent : baseEnd_2045416 < baseStart_2045416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045433 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 3]
def baseStart_2045433 : Nat := 118140960795 + 2045433 * 2 ^ 59
def prefixEnd_2045433 : Nat := 4983230072969 + 3 ^ 40 * 2045433 * 2
def baseEnd_2045433 : Nat := 466795678030222652302547

theorem tailTrace_2045433 : CollatzResearch.WordTrace tailWord_2045433 prefixEnd_2045433 466795678030222652302547 := by
  unfold tailWord_2045433
  simp only [CollatzResearch.WordTrace]
  refine ⟨74603070398753047989756953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49735380265835365326504635 74603070398753047989756953)
  ·
    refine ⟨55952302799064785992317715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74603070398753047989756953 55952302799064785992317715)
    ·
      refine ⟨83928454198597178988476573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55952302799064785992317715 83928454198597178988476573)
      ·
        refine ⟨31473170324473942120678715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83928454198597178988476573 31473170324473942120678715)
        ·
          refine ⟨47209755486710913181018073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31473170324473942120678715 47209755486710913181018073)
          ·
            refine ⟨35407316615033184885763555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47209755486710913181018073 35407316615033184885763555)
            ·
              refine ⟨53110974922549777328645333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35407316615033184885763555 53110974922549777328645333)
              ·
                refine ⟨1244788474747260406140125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53110974922549777328645333 1244788474747260406140125)
                ·
                  refine ⟨466795678030222652302547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244788474747260406140125 466795678030222652302547)
                  ·
                    rfl

theorem cell21_2045433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_2045433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045433 prefixEnd_2045433 := by exact prefixLift 2045433
  have htrace : WordTrace (prefixWord ++ tailWord_2045433) baseStart_2045433 baseEnd_2045433 := by
    simpa [prefixWord, tailWord_2045433, baseEnd_2045433] using wordTrace_append hprefix tailTrace_2045433
  have hstable : (prefixWord ++ tailWord_2045433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045433).length < 2 ^ (prefixWord ++ tailWord_2045433).sum := by decide
  have hdescent : baseEnd_2045433 < baseStart_2045433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045450 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_2045450 : Nat := 118140960795 + 2045450 * 2 ^ 59
def prefixEnd_2045450 : Nat := 4983230072969 + 3 ^ 40 * 2045450 * 2
def baseEnd_2045450 : Nat := 466799557661834400519179

theorem tailTrace_2045450 : CollatzResearch.WordTrace tailWord_2045450 prefixEnd_2045450 466799557661834400519179 := by
  unfold tailWord_2045450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18650922609922864973281451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49735793626460973262083869 18650922609922864973281451)
  ·
    refine ⟨27976383914884297459922177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18650922609922864973281451 27976383914884297459922177)
    ·
      refine ⟨20982287936163223094941633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27976383914884297459922177 20982287936163223094941633)
      ·
        refine ⟨15736715952122417321206225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20982287936163223094941633 15736715952122417321206225)
        ·
          refine ⟨11802536964091812990904669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15736715952122417321206225 11802536964091812990904669)
          ·
            refine ⟨4425951361534429871589251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11802536964091812990904669 4425951361534429871589251)
            ·
              refine ⟨6638927042301644807383877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425951361534429871589251 6638927042301644807383877)
              ·
                refine ⟨1244798820431558401384477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6638927042301644807383877 1244798820431558401384477)
                ·
                  refine ⟨466799557661834400519179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244798820431558401384477 466799557661834400519179)
                  ·
                    rfl

theorem cell21_2045450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_2045450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045450 prefixEnd_2045450 := by exact prefixLift 2045450
  have htrace : WordTrace (prefixWord ++ tailWord_2045450) baseStart_2045450 baseEnd_2045450 := by
    simpa [prefixWord, tailWord_2045450, baseEnd_2045450] using wordTrace_append hprefix tailTrace_2045450
  have hstable : (prefixWord ++ tailWord_2045450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045450).length < 2 ^ (prefixWord ++ tailWord_2045450).sum := by decide
  have hdescent : baseEnd_2045450 < baseStart_2045450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045453 : List Nat := [1, 7, 1, 1, 2, 2, 1, 6]
def baseStart_2045453 : Nat := 118140960795 + 2045453 * 2 ^ 59
def prefixEnd_2045453 : Nat := 4983230072969 + 3 ^ 40 * 2045453 * 2
def baseEnd_2045453 : Nat := 155600080767569020656391

theorem tailTrace_2045453 : CollatzResearch.WordTrace tailWord_2045453 prefixEnd_2045453 155600080767569020656391 := by
  unfold tailWord_2045453
  simp only [CollatzResearch.WordTrace]
  refine ⟨74603799858680591405485013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49735866572453727603656675 74603799858680591405485013)
  ·
    refine ⟨1748526559187826361066055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74603799858680591405485013 1748526559187826361066055)
    ·
      refine ⟨2622789838781739541599083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1748526559187826361066055 2622789838781739541599083)
      ·
        refine ⟨3934184758172609312398625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622789838781739541599083 3934184758172609312398625)
        ·
          refine ⟨2950638568629456984298969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934184758172609312398625 2950638568629456984298969)
          ·
            refine ⟨2212978926472092738224227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2950638568629456984298969 2212978926472092738224227)
            ·
              refine ⟨3319468389708139107336341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212978926472092738224227 3319468389708139107336341)
              ·
                refine ⟨155600080767569020656391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3319468389708139107336341 155600080767569020656391)
                ·
                  rfl

theorem cell21_2045453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 6].length) (baseStart_2045453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045453 prefixEnd_2045453 := by exact prefixLift 2045453
  have htrace : WordTrace (prefixWord ++ tailWord_2045453) baseStart_2045453 baseEnd_2045453 := by
    simpa [prefixWord, tailWord_2045453, baseEnd_2045453] using wordTrace_append hprefix tailTrace_2045453
  have hstable : (prefixWord ++ tailWord_2045453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045453).length < 2 ^ (prefixWord ++ tailWord_2045453).sum := by decide
  have hdescent : baseEnd_2045453 < baseStart_2045453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045470 : List Nat := [4, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2045470 : Nat := 118140960795 + 2045470 * 2 ^ 59
def prefixEnd_2045470 : Nat := 4983230072969 + 3 ^ 40 * 2045470 * 2
def baseEnd_2045470 : Nat := 155601373978106270061935

theorem tailTrace_2045470 : CollatzResearch.WordTrace tailWord_2045470 prefixEnd_2045470 155601373978106270061935 := by
  unfold tailWord_2045470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325552487452375413606733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49736279933079335539235909 9325552487452375413606733)
  ·
    refine ⟨3497082182794640780102525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9325552487452375413606733 3497082182794640780102525)
    ·
      refine ⟨1311405818547990292538447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3497082182794640780102525 1311405818547990292538447)
      ·
        refine ⟨1967108727821985438807671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311405818547990292538447 1967108727821985438807671)
        ·
          refine ⟨2950663091732978158211507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967108727821985438807671 2950663091732978158211507)
          ·
            refine ⟨4425994637599467237317261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950663091732978158211507 4425994637599467237317261)
            ·
              refine ⟨1659747989099800213993973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4425994637599467237317261 1659747989099800213993973)
              ·
                refine ⟨155601373978106270061935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659747989099800213993973 155601373978106270061935)
                ·
                  rfl

theorem cell21_2045470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2045470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045470 prefixEnd_2045470 := by exact prefixLift 2045470
  have htrace : WordTrace (prefixWord ++ tailWord_2045470) baseStart_2045470 baseEnd_2045470 := by
    simpa [prefixWord, tailWord_2045470, baseEnd_2045470] using wordTrace_append hprefix tailTrace_2045470
  have hstable : (prefixWord ++ tailWord_2045470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045470).length < 2 ^ (prefixWord ++ tailWord_2045470).sum := by decide
  have hdescent : baseEnd_2045470 < baseStart_2045470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045509 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 3]
def baseStart_2045509 : Nat := 118140960795 + 2045509 * 2 ^ 59
def prefixEnd_2045509 : Nat := 4983230072969 + 3 ^ 40 * 2045509 * 2
def baseEnd_2045509 : Nat := 466813022265663409035725

theorem tailTrace_2045509 : CollatzResearch.WordTrace tailWord_2045509 prefixEnd_2045509 466813022265663409035725 := by
  unfold tailWord_2045509
  simp only [CollatzResearch.WordTrace]
  refine ⟨74605842346477712969523581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49737228230985141979682387 74605842346477712969523581)
  ·
    refine ⟨27977190879929142363571343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74605842346477712969523581 27977190879929142363571343)
    ·
      refine ⟨41965786319893713545357015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27977190879929142363571343 41965786319893713545357015)
      ·
        refine ⟨62948679479840570318035523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41965786319893713545357015 62948679479840570318035523)
        ·
          refine ⟨94423019219760855477053285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62948679479840570318035523 94423019219760855477053285)
          ·
            refine ⟨17704316103705160401947491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94423019219760855477053285 17704316103705160401947491)
            ·
              refine ⟨26556474155557740602921237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17704316103705160401947491 26556474155557740602921237)
              ·
                refine ⟨1244834726041769090761933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26556474155557740602921237 1244834726041769090761933)
                ·
                  refine ⟨466813022265663409035725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244834726041769090761933 466813022265663409035725)
                  ·
                    rfl

theorem cell21_2045509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_2045509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045509 prefixEnd_2045509 := by exact prefixLift 2045509
  have htrace : WordTrace (prefixWord ++ tailWord_2045509) baseStart_2045509 baseEnd_2045509 := by
    simpa [prefixWord, tailWord_2045509, baseEnd_2045509] using wordTrace_append hprefix tailTrace_2045509
  have hstable : (prefixWord ++ tailWord_2045509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045509).length < 2 ^ (prefixWord ++ tailWord_2045509).sum := by decide
  have hdescent : baseEnd_2045509 < baseStart_2045509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045537 : List Nat := [1, 2, 3, 1, 1, 3, 3, 7]
def baseStart_2045537 : Nat := 118140960795 + 2045537 * 2 ^ 59
def prefixEnd_2045537 : Nat := 4983230072969 + 3 ^ 40 * 2045537 * 2
def baseEnd_2045537 : Nat := 155606470749047194189667

theorem tailTrace_2045537 : CollatzResearch.WordTrace tailWord_2045537 prefixEnd_2045537 155606470749047194189667 := by
  unfold tailWord_2045537
  simp only [CollatzResearch.WordTrace]
  refine ⟨74606863590376273751542865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49737909060250849167695243 74606863590376273751542865)
  ·
    refine ⟨55955147692782205313657149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74606863590376273751542865 55955147692782205313657149)
    ·
      refine ⟨20983180384793326992621431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55955147692782205313657149 20983180384793326992621431)
      ·
        refine ⟨31474770577189990488932147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20983180384793326992621431 31474770577189990488932147)
        ·
          refine ⟨47212155865784985733398221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31474770577189990488932147 47212155865784985733398221)
          ·
            refine ⟨17704558449669369650024333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47212155865784985733398221 17704558449669369650024333)
            ·
              refine ⟨6639209418626013618759125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17704558449669369650024333 6639209418626013618759125)
              ·
                refine ⟨155606470749047194189667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6639209418626013618759125 155606470749047194189667)
                ·
                  rfl

theorem cell21_2045537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_2045537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045537 prefixEnd_2045537 := by exact prefixLift 2045537
  have htrace : WordTrace (prefixWord ++ tailWord_2045537) baseStart_2045537 baseEnd_2045537 := by
    simpa [prefixWord, tailWord_2045537, baseEnd_2045537] using wordTrace_append hprefix tailTrace_2045537
  have hstable : (prefixWord ++ tailWord_2045537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045537).length < 2 ^ (prefixWord ++ tailWord_2045537).sum := by decide
  have hdescent : baseEnd_2045537 < baseStart_2045537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045554 : List Nat := [3, 2, 1, 2, 3, 3, 7]
def baseStart_2045554 : Nat := 118140960795 + 2045554 * 2 ^ 59
def prefixEnd_2045554 : Nat := 4983230072969 + 3 ^ 40 * 2045554 * 2
def baseEnd_2045554 : Nat := 51869254653194814531737

theorem tailTrace_2045554 : CollatzResearch.WordTrace tailWord_2045554 prefixEnd_2045554 51869254653194814531737 := by
  unfold tailWord_2045554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18651870907828671413727929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49738322420876457103274477 18651870907828671413727929)
  ·
    refine ⟨13988903180871503560295947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18651870907828671413727929 13988903180871503560295947)
    ·
      refine ⟨20983354771307255340443921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13988903180871503560295947 20983354771307255340443921)
      ·
        refine ⟨15737516078480441505332941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20983354771307255340443921 15737516078480441505332941)
        ·
          refine ⟨5901568529430165564499853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15737516078480441505332941 5901568529430165564499853)
          ·
            refine ⟨2213088198536312086687445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5901568529430165564499853 2213088198536312086687445)
            ·
              refine ⟨51869254653194814531737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2213088198536312086687445 51869254653194814531737)
              ·
                rfl

theorem cell21_2045554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 7].length) (baseStart_2045554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045554 prefixEnd_2045554 := by exact prefixLift 2045554
  have htrace : WordTrace (prefixWord ++ tailWord_2045554) baseStart_2045554 baseEnd_2045554 := by
    simpa [prefixWord, tailWord_2045554, baseEnd_2045554] using wordTrace_append hprefix tailTrace_2045554
  have hstable : (prefixWord ++ tailWord_2045554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045554).length < 2 ^ (prefixWord ++ tailWord_2045554).sum := by decide
  have hdescent : baseEnd_2045554 < baseStart_2045554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045627 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_2045627 : Nat := 118140960795 + 2045627 * 2 ^ 59
def prefixEnd_2045627 : Nat := 4983230072969 + 3 ^ 40 * 2045627 * 2
def baseEnd_2045627 : Nat := 466839951473321426068817

theorem tailTrace_2045627 : CollatzResearch.WordTrace tailWord_2045627 prefixEnd_2045627 466839951473321426068817 := by
  unfold tailWord_2045627
  simp only [CollatzResearch.WordTrace]
  refine ⟨74610146160050219122319135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49740097440033479414879423 74610146160050219122319135)
  ·
    refine ⟨111915219240075328683478703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74610146160050219122319135 111915219240075328683478703)
    ·
      refine ⟨167872828860112993025218055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111915219240075328683478703 167872828860112993025218055)
      ·
        refine ⟨251809243290169489537827083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167872828860112993025218055 251809243290169489537827083)
        ·
          refine ⟨377713864935254234306740625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251809243290169489537827083 377713864935254234306740625)
          ·
            refine ⟨283285398701440675730055469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377713864935254234306740625 283285398701440675730055469)
            ·
              refine ⟨106232024513040253398770801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283285398701440675730055469 106232024513040253398770801)
              ·
                refine ⟨79674018384780190049078101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106232024513040253398770801 79674018384780190049078101)
                ·
                  refine ⟨466839951473321426068817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79674018384780190049078101 466839951473321426068817)
                  ·
                    rfl

theorem cell21_2045627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_2045627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045627 prefixEnd_2045627 := by exact prefixLift 2045627
  have htrace : WordTrace (prefixWord ++ tailWord_2045627) baseStart_2045627 baseEnd_2045627 := by
    simpa [prefixWord, tailWord_2045627, baseEnd_2045627] using wordTrace_append hprefix tailTrace_2045627
  have hstable : (prefixWord ++ tailWord_2045627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045627).length < 2 ^ (prefixWord ++ tailWord_2045627).sum := by decide
  have hdescent : baseEnd_2045627 < baseStart_2045627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045630 : List Nat := [4, 2, 1, 1, 2, 2, 3, 6]
def baseStart_2045630 : Nat := 118140960795 + 2045630 * 2 ^ 59
def prefixEnd_2045630 : Nat := 4983230072969 + 3 ^ 40 * 2045630 * 2
def baseEnd_2045630 : Nat := 155613545371398029172937

theorem tailTrace_2045630 : CollatzResearch.WordTrace tailWord_2045630 prefixEnd_2045630 155613545371398029172937 := by
  unfold tailWord_2045630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326281947379918829334793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49740170386026233756452229 9326281947379918829334793)
  ·
    refine ⟨6994711460534939122001095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9326281947379918829334793 6994711460534939122001095)
    ·
      refine ⟨10492067190802408683001643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994711460534939122001095 10492067190802408683001643)
      ·
        refine ⟨15738100786203613024502465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10492067190802408683001643 15738100786203613024502465)
        ·
          refine ⟨11803575589652709768376849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15738100786203613024502465 11803575589652709768376849)
          ·
            refine ⟨8852681692239532326282637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11803575589652709768376849 8852681692239532326282637)
            ·
              refine ⟨3319755634589824622355989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8852681692239532326282637 3319755634589824622355989)
              ·
                refine ⟨155613545371398029172937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3319755634589824622355989 155613545371398029172937)
                ·
                  rfl

theorem cell21_2045630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_2045630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045630 prefixEnd_2045630 := by exact prefixLift 2045630
  have htrace : WordTrace (prefixWord ++ tailWord_2045630) baseStart_2045630 baseEnd_2045630 := by
    simpa [prefixWord, tailWord_2045630, baseEnd_2045630] using wordTrace_append hprefix tailTrace_2045630
  have hstable : (prefixWord ++ tailWord_2045630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045630).length < 2 ^ (prefixWord ++ tailWord_2045630).sum := by decide
  have hdescent : baseEnd_2045630 < baseStart_2045630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045675 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_2045675 : Nat := 118140960795 + 2045675 * 2 ^ 59
def prefixEnd_2045675 : Nat := 4983230072969 + 3 ^ 40 * 2045675 * 2
def baseEnd_2045675 : Nat := 466850905727284009268719

theorem tailTrace_2045675 : CollatzResearch.WordTrace tailWord_2045675 prefixEnd_2045675 466850905727284009268719 := by
  unfold tailWord_2045675
  simp only [CollatzResearch.WordTrace]
  refine ⟨74611896863876323320066479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49741264575917548880044319 74611896863876323320066479)
  ·
    refine ⟨111917845295814484980099719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74611896863876323320066479 111917845295814484980099719)
    ·
      refine ⟨167876767943721727470149579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111917845295814484980099719 167876767943721727470149579)
      ·
        refine ⟨251815151915582591205224369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167876767943721727470149579 251815151915582591205224369)
        ·
          refine ⟨188861363936686943403918277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251815151915582591205224369 188861363936686943403918277)
          ·
            refine ⟨35411505738128801888234677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188861363936686943403918277 35411505738128801888234677)
            ·
              refine ⟨3319828662949575177022001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35411505738128801888234677 3319828662949575177022001)
              ·
                refine ⟨2489871497212181382766501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319828662949575177022001 2489871497212181382766501)
                ·
                  refine ⟨466850905727284009268719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489871497212181382766501 466850905727284009268719)
                  ·
                    rfl

theorem cell21_2045675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_2045675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045675 prefixEnd_2045675 := by exact prefixLift 2045675
  have htrace : WordTrace (prefixWord ++ tailWord_2045675) baseStart_2045675 baseEnd_2045675 := by
    simpa [prefixWord, tailWord_2045675, baseEnd_2045675] using wordTrace_append hprefix tailTrace_2045675
  have hstable : (prefixWord ++ tailWord_2045675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045675).length < 2 ^ (prefixWord ++ tailWord_2045675).sum := by decide
  have hdescent : baseEnd_2045675 < baseStart_2045675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045692 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_2045692 : Nat := 118140960795 + 2045692 * 2 ^ 59
def prefixEnd_2045692 : Nat := 4983230072969 + 3 ^ 40 * 2045692 * 2
def baseEnd_2045692 : Nat := 466854785358895757485351

theorem tailTrace_2045692 : CollatzResearch.WordTrace tailWord_2045692 prefixEnd_2045692 466854785358895757485351 := by
  unfold tailWord_2045692
  simp only [CollatzResearch.WordTrace]
  refine ⟨37306258452407367611717665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49741677936543156815623553 37306258452407367611717665)
  ·
    refine ⟨27979693839305525708788249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37306258452407367611717665 27979693839305525708788249)
    ·
      refine ⟨20984770379479144281591187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27979693839305525708788249 20984770379479144281591187)
      ·
        refine ⟨31477155569218716422386781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984770379479144281591187 31477155569218716422386781)
        ·
          refine ⟨11803933338457018658395043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31477155569218716422386781 11803933338457018658395043)
          ·
            refine ⟨17705900007685527987592565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803933338457018658395043 17705900007685527987592565)
            ·
              refine ⟨1659928125720518248836803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17705900007685527987592565 1659928125720518248836803)
              ·
                refine ⟨2489892188580777373255205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659928125720518248836803 2489892188580777373255205)
                ·
                  refine ⟨466854785358895757485351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2489892188580777373255205 466854785358895757485351)
                  ·
                    rfl

theorem cell21_2045692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_2045692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045692 prefixEnd_2045692 := by exact prefixLift 2045692
  have htrace : WordTrace (prefixWord ++ tailWord_2045692) baseStart_2045692 baseEnd_2045692 := by
    simpa [prefixWord, tailWord_2045692, baseEnd_2045692] using wordTrace_append hprefix tailTrace_2045692
  have hstable : (prefixWord ++ tailWord_2045692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045692).length < 2 ^ (prefixWord ++ tailWord_2045692).sum := by decide
  have hdescent : baseEnd_2045692 < baseStart_2045692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045706 : List Nat := [3, 1, 2, 2, 1, 3, 4, 5]
def baseStart_2045706 : Nat := 118140960795 + 2045706 * 2 ^ 59
def prefixEnd_2045706 : Nat := 4983230072969 + 3 ^ 40 * 2045706 * 2
def baseEnd_2045706 : Nat := 155619326783211614750663

theorem tailTrace_2045706 : CollatzResearch.WordTrace tailWord_2045706 prefixEnd_2045706 155619326783211614750663 := by
  unfold tailWord_2045706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18653256881691003903611243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49742018351176010409629981 18653256881691003903611243)
  ·
    refine ⟨27979885322536505855416865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18653256881691003903611243 27979885322536505855416865)
    ·
      refine ⟨20984913991902379391562649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27979885322536505855416865 20984913991902379391562649)
      ·
        refine ⟨15738685493926784543671987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20984913991902379391562649 15738685493926784543671987)
        ·
          refine ⟨23608028240890176815507981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15738685493926784543671987 23608028240890176815507981)
          ·
            refine ⟨8853010590333816305815493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23608028240890176815507981 8853010590333816305815493)
            ·
              refine ⟨1659939485687590557340405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8853010590333816305815493 1659939485687590557340405)
              ·
                refine ⟨155619326783211614750663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1659939485687590557340405 155619326783211614750663)
                ·
                  rfl

theorem cell21_2045706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_2045706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045706 prefixEnd_2045706 := by exact prefixLift 2045706
  have htrace : WordTrace (prefixWord ++ tailWord_2045706) baseStart_2045706 baseEnd_2045706 := by
    simpa [prefixWord, tailWord_2045706, baseEnd_2045706] using wordTrace_append hprefix tailTrace_2045706
  have hstable : (prefixWord ++ tailWord_2045706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045706).length < 2 ^ (prefixWord ++ tailWord_2045706).sum := by decide
  have hdescent : baseEnd_2045706 < baseStart_2045706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045788 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_2045788 : Nat := 118140960795 + 2045788 * 2 ^ 59
def prefixEnd_2045788 : Nat := 4983230072969 + 3 ^ 40 * 2045788 * 2
def baseEnd_2045788 : Nat := 466876693866820923885155

theorem tailTrace_2045788 : CollatzResearch.WordTrace tailWord_2045788 prefixEnd_2045788 466876693866820923885155 := by
  unfold tailWord_2045788
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308009156233471809465009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49744012208311295745953345 37308009156233471809465009)
  ·
    refine ⟨27981006867175103857098757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37308009156233471809465009 27981006867175103857098757)
    ·
      refine ⟨5246438787595331973206017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27981006867175103857098757 5246438787595331973206017)
      ·
        refine ⟨3934829090696498979904513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5246438787595331973206017 3934829090696498979904513)
        ·
          refine ⟨2951121818022374234928385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934829090696498979904513 2951121818022374234928385)
          ·
            refine ⟨2213341363516780676196289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951121818022374234928385 2213341363516780676196289)
            ·
              refine ⟨1660006022637585507147217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213341363516780676196289 1660006022637585507147217)
              ·
                refine ⟨1245004516978189130360413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660006022637585507147217 1245004516978189130360413)
                ·
                  refine ⟨466876693866820923885155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245004516978189130360413 466876693866820923885155)
                  ·
                    rfl

theorem cell21_2045788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_2045788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045788 prefixEnd_2045788 := by exact prefixLift 2045788
  have htrace : WordTrace (prefixWord ++ tailWord_2045788) baseStart_2045788 baseEnd_2045788 := by
    simpa [prefixWord, tailWord_2045788, baseEnd_2045788] using wordTrace_append hprefix tailTrace_2045788
  have hstable : (prefixWord ++ tailWord_2045788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045788).length < 2 ^ (prefixWord ++ tailWord_2045788).sum := by decide
  have hdescent : baseEnd_2045788 < baseStart_2045788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045810 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2045810 : Nat := 118140960795 + 2045810 * 2 ^ 59
def prefixEnd_2045810 : Nat := 4983230072969 + 3 ^ 40 * 2045810 * 2
def baseEnd_2045810 : Nat := 466881714566553774518443

theorem tailTrace_2045810 : CollatzResearch.WordTrace tailWord_2045810 prefixEnd_2045810 466881714566553774518443 := by
  unfold tailWord_2045810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654205179596810344057721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49744547145591494250820589 18654205179596810344057721)
  ·
    refine ⟨13990653884697607758043291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18654205179596810344057721 13990653884697607758043291)
    ·
      refine ⟨20985980827046411637064937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13990653884697607758043291 20985980827046411637064937)
      ·
        refine ⟨15739485620284808727798703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20985980827046411637064937 15739485620284808727798703)
        ·
          refine ⟨23609228430427213091698055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15739485620284808727798703 23609228430427213091698055)
          ·
            refine ⟨35413842645640819637547083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23609228430427213091698055 35413842645640819637547083)
            ·
              refine ⟨53120763968461229456320625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35413842645640819637547083 53120763968461229456320625)
              ·
                refine ⟨39840572976345922092240469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53120763968461229456320625 39840572976345922092240469)
                ·
                  refine ⟨466881714566553774518443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39840572976345922092240469 466881714566553774518443)
                  ·
                    rfl

theorem cell21_2045810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2045810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045810 prefixEnd_2045810 := by exact prefixLift 2045810
  have htrace : WordTrace (prefixWord ++ tailWord_2045810) baseStart_2045810 baseEnd_2045810 := by
    simpa [prefixWord, tailWord_2045810, baseEnd_2045810] using wordTrace_append hprefix tailTrace_2045810
  have hstable : (prefixWord ++ tailWord_2045810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045810).length < 2 ^ (prefixWord ++ tailWord_2045810).sum := by decide
  have hdescent : baseEnd_2045810 < baseStart_2045810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045844 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2045844 : Nat := 118140960795 + 2045844 * 2 ^ 59
def prefixEnd_2045844 : Nat := 4983230072969 + 3 ^ 40 * 2045844 * 2
def baseEnd_2045844 : Nat := 466889473829777270951707

theorem tailTrace_2045844 : CollatzResearch.WordTrace tailWord_2045844 prefixEnd_2045844 466889473829777270951707 := by
  unfold tailWord_2045844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37309030400132032591484293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49745373866842710121979057 37309030400132032591484293)
  ·
    refine ⟨6995443200024756110903305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37309030400132032591484293 6995443200024756110903305)
    ·
      refine ⟨5246582400018567083177479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6995443200024756110903305 5246582400018567083177479)
      ·
        refine ⟨7869873600027850624766219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246582400018567083177479 7869873600027850624766219)
        ·
          refine ⟨11804810400041775937149329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869873600027850624766219 11804810400041775937149329)
          ·
            refine ⟨8853607800031331952861997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11804810400041775937149329 8853607800031331952861997)
            ·
              refine ⟨3320102925011749482323249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8853607800031331952861997 3320102925011749482323249)
              ·
                refine ⟨2490077193758812111742437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3320102925011749482323249 2490077193758812111742437)
                ·
                  refine ⟨466889473829777270951707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490077193758812111742437 466889473829777270951707)
                  ·
                    rfl

theorem cell21_2045844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2045844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045844 prefixEnd_2045844 := by exact prefixLift 2045844
  have htrace : WordTrace (prefixWord ++ tailWord_2045844) baseStart_2045844 baseEnd_2045844 := by
    simpa [prefixWord, tailWord_2045844, baseEnd_2045844] using wordTrace_append hprefix tailTrace_2045844
  have hstable : (prefixWord ++ tailWord_2045844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045844).length < 2 ^ (prefixWord ++ tailWord_2045844).sum := by decide
  have hdescent : baseEnd_2045844 < baseStart_2045844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045906 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_2045906 : Nat := 118140960795 + 2045906 * 2 ^ 59
def prefixEnd_2045906 : Nat := 4983230072969 + 3 ^ 40 * 2045906 * 2
def baseEnd_2045906 : Nat := 466903623074478940918247

theorem tailTrace_2045906 : CollatzResearch.WordTrace tailWord_2045906 prefixEnd_2045906 466903623074478940918247 := by
  unfold tailWord_2045906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655080531509862442931393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49746881417359633181150381 18655080531509862442931393)
  ·
    refine ⟨13991310398632396832198545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18655080531509862442931393 13991310398632396832198545)
    ·
      refine ⟨10493482798974297624148909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13991310398632396832198545 10493482798974297624148909)
      ·
        refine ⟨3935056049615361609055841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10493482798974297624148909 3935056049615361609055841)
        ·
          refine ⟨2951292037211521206791881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935056049615361609055841 2951292037211521206791881)
          ·
            refine ⟨2213469027908640905093911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951292037211521206791881 2213469027908640905093911)
            ·
              refine ⟨3320203541862961357640867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213469027908640905093911 3320203541862961357640867)
              ·
                refine ⟨4980305312794442036461301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320203541862961357640867 4980305312794442036461301)
                ·
                  refine ⟨466903623074478940918247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980305312794442036461301 466903623074478940918247)
                  ·
                    rfl

theorem cell21_2045906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_2045906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045906 prefixEnd_2045906 := by exact prefixLift 2045906
  have htrace : WordTrace (prefixWord ++ tailWord_2045906) baseStart_2045906 baseEnd_2045906 := by
    simpa [prefixWord, tailWord_2045906, baseEnd_2045906] using wordTrace_append hprefix tailTrace_2045906
  have hstable : (prefixWord ++ tailWord_2045906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045906).length < 2 ^ (prefixWord ++ tailWord_2045906).sum := by decide
  have hdescent : baseEnd_2045906 < baseStart_2045906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045931 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_2045931 : Nat := 118140960795 + 2045931 * 2 ^ 59
def prefixEnd_2045931 : Nat := 4983230072969 + 3 ^ 40 * 2045931 * 2
def baseEnd_2045931 : Nat := 466909328415084453001529

theorem tailTrace_2045931 : CollatzResearch.WordTrace tailWord_2045931 prefixEnd_2045931 466909328415084453001529 := by
  unfold tailWord_2045931
  simp only [CollatzResearch.WordTrace]
  refine ⟨74621233950948879041385647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49747489300632586027590431 74621233950948879041385647)
  ·
    refine ⟨111931850926423318562078471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74621233950948879041385647 111931850926423318562078471)
    ·
      refine ⟨167897776389634977843117707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111931850926423318562078471 167897776389634977843117707)
      ·
        refine ⟨251846664584452466764676561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167897776389634977843117707 251846664584452466764676561)
        ·
          refine ⟨188884998438339350073507421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251846664584452466764676561 188884998438339350073507421)
          ·
            refine ⟨70831874414377256277565283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188884998438339350073507421 70831874414377256277565283)
            ·
              refine ⟨106247811621565884416347925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70831874414377256277565283 106247811621565884416347925)
              ·
                refine ⟨4980366169760900832016309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106247811621565884416347925 4980366169760900832016309)
                ·
                  refine ⟨466909328415084453001529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980366169760900832016309 466909328415084453001529)
                  ·
                    rfl

theorem cell21_2045931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_2045931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2045931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2045931 prefixEnd_2045931 := by exact prefixLift 2045931
  have htrace : WordTrace (prefixWord ++ tailWord_2045931) baseStart_2045931 baseEnd_2045931 := by
    simpa [prefixWord, tailWord_2045931, baseEnd_2045931] using wordTrace_append hprefix tailTrace_2045931
  have hstable : (prefixWord ++ tailWord_2045931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045931).length < 2 ^ (prefixWord ++ tailWord_2045931).sum := by decide
  have hdescent : baseEnd_2045931 < baseStart_2045931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046159 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_2046159 : Nat := 118140960795 + 2046159 * 2 ^ 59
def prefixEnd_2046159 : Nat := 4983230072969 + 3 ^ 40 * 2046159 * 2
def baseEnd_2046159 : Nat := 466961361121406723201063

theorem tailTrace_2046159 : CollatzResearch.WordTrace tailWord_2046159 prefixEnd_2046159 466961361121406723201063 := by
  unfold tailWord_2046159
  simp only [CollatzResearch.WordTrace]
  refine ⟨74629549794122873980685531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49753033196081915987123687 74629549794122873980685531)
  ·
    refine ⟨111944324691184310971028297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74629549794122873980685531 111944324691184310971028297)
    ·
      refine ⟨83958243518388233228271223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111944324691184310971028297 83958243518388233228271223)
      ·
        refine ⟨125937365277582349842406835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83958243518388233228271223 125937365277582349842406835)
        ·
          refine ⟨188906047916373524763610253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125937365277582349842406835 188906047916373524763610253)
          ·
            refine ⟨70839767968640071786353845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188906047916373524763610253 70839767968640071786353845)
            ·
              refine ⟨6641228247060006729970673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70839767968640071786353845 6641228247060006729970673)
              ·
                refine ⟨4980921185295005047478005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6641228247060006729970673 4980921185295005047478005)
                ·
                  refine ⟨466961361121406723201063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4980921185295005047478005 466961361121406723201063)
                  ·
                    rfl

theorem cell21_2046159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_2046159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046159 prefixEnd_2046159 := by exact prefixLift 2046159
  have htrace : WordTrace (prefixWord ++ tailWord_2046159) baseStart_2046159 baseEnd_2046159 := by
    simpa [prefixWord, tailWord_2046159, baseEnd_2046159] using wordTrace_append hprefix tailTrace_2046159
  have hstable : (prefixWord ++ tailWord_2046159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046159).length < 2 ^ (prefixWord ++ tailWord_2046159).sum := by decide
  have hdescent : baseEnd_2046159 < baseStart_2046159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046162 : List Nat := [3, 2, 2, 2, 1, 3, 3, 5]
def baseStart_2046162 : Nat := 118140960795 + 2046162 * 2 ^ 59
def prefixEnd_2046162 : Nat := 4983230072969 + 3 ^ 40 * 2046162 * 2
def baseEnd_2046162 : Nat := 155654015254093128217019

theorem tailTrace_2046162 : CollatzResearch.WordTrace tailWord_2046162 prefixEnd_2046162 155654015254093128217019 := by
  unfold tailWord_2046162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18657414803278001373261185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49753106142074670328696493 18657414803278001373261185)
  ·
    refine ⟨13993061102458501029945889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18657414803278001373261185 13993061102458501029945889)
    ·
      refine ⟨10494795826843875772459417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13993061102458501029945889 10494795826843875772459417)
      ·
        refine ⟨7871096870132906829344563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10494795826843875772459417 7871096870132906829344563)
        ·
          refine ⟨11806645305199360244016845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871096870132906829344563 11806645305199360244016845)
          ·
            refine ⟨4427491989449760091506317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11806645305199360244016845 4427491989449760091506317)
            ·
              refine ⟨1660309496043660034314869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4427491989449760091506317 1660309496043660034314869)
              ·
                refine ⟨155654015254093128217019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1660309496043660034314869 155654015254093128217019)
                ·
                  rfl

theorem cell21_2046162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_2046162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046162 prefixEnd_2046162 := by exact prefixLift 2046162
  have htrace : WordTrace (prefixWord ++ tailWord_2046162) baseStart_2046162 baseEnd_2046162 := by
    simpa [prefixWord, tailWord_2046162, baseEnd_2046162] using wordTrace_append hprefix tailTrace_2046162
  have hstable : (prefixWord ++ tailWord_2046162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046162).length < 2 ^ (prefixWord ++ tailWord_2046162).sum := by decide
  have hdescent : baseEnd_2046162 < baseStart_2046162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046207 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 4]
def baseStart_2046207 : Nat := 118140960795 + 2046207 * 2 ^ 59
def prefixEnd_2046207 : Nat := 4983230072969 + 3 ^ 40 * 2046207 * 2
def baseEnd_2046207 : Nat := 466972315375369306400965

theorem tailTrace_2046207 : CollatzResearch.WordTrace tailWord_2046207 prefixEnd_2046207 466972315375369306400965 := by
  unfold tailWord_2046207
  simp only [CollatzResearch.WordTrace]
  refine ⟨74631300497948978178432875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49754200331965985452288583 74631300497948978178432875)
  ·
    refine ⟨111946950746923467267649313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74631300497948978178432875 111946950746923467267649313)
    ·
      refine ⟨83960213060192600450736985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111946950746923467267649313 83960213060192600450736985)
      ·
        refine ⟨62970159795144450338052739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83960213060192600450736985 62970159795144450338052739)
        ·
          refine ⟨94455239692716675507079109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62970159795144450338052739 94455239692716675507079109)
          ·
            refine ⟨17710357442384376657577333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94455239692716675507079109 17710357442384376657577333)
            ·
              refine ⟨1660346010223535311647875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17710357442384376657577333 1660346010223535311647875)
              ·
                refine ⟨2490519015335302967471813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660346010223535311647875 2490519015335302967471813)
                ·
                  refine ⟨466972315375369306400965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490519015335302967471813 466972315375369306400965)
                  ·
                    rfl

theorem cell21_2046207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4].length) (baseStart_2046207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046207 prefixEnd_2046207 := by exact prefixLift 2046207
  have htrace : WordTrace (prefixWord ++ tailWord_2046207) baseStart_2046207 baseEnd_2046207 := by
    simpa [prefixWord, tailWord_2046207, baseEnd_2046207] using wordTrace_append hprefix tailTrace_2046207
  have hstable : (prefixWord ++ tailWord_2046207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046207).length < 2 ^ (prefixWord ++ tailWord_2046207).sum := by decide
  have hdescent : baseEnd_2046207 < baseStart_2046207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046238 : List Nat := [4, 3, 2, 1, 1, 1, 9]
def baseStart_2046238 : Nat := 118140960795 + 2046238 * 2 ^ 59
def prefixEnd_2046238 : Nat := 4983230072969 + 3 ^ 40 * 2046238 * 2
def baseEnd_2046238 : Nat := 51886598888635571264915

theorem tailTrace_2046238 : CollatzResearch.WordTrace tailWord_2046238 prefixEnd_2046238 51886598888635571264915 := by
  unfold tailWord_2046238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329053895104583809101421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49754954107224446981874245 9329053895104583809101421)
  ·
    refine ⟨3498395210664218928413033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9329053895104583809101421 3498395210664218928413033)
    ·
      refine ⟨2623796407998164196309775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3498395210664218928413033 2623796407998164196309775)
      ·
        refine ⟨3935694611997246294464663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623796407998164196309775 3935694611997246294464663)
        ·
          refine ⟨5903541917995869441696995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935694611997246294464663 5903541917995869441696995)
          ·
            refine ⟨8855312876993804162545493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903541917995869441696995 8855312876993804162545493)
            ·
              refine ⟨51886598888635571264915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8855312876993804162545493 51886598888635571264915)
              ·
                rfl

theorem cell21_2046238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 9].length) (baseStart_2046238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046238 prefixEnd_2046238 := by exact prefixLift 2046238
  have htrace : WordTrace (prefixWord ++ tailWord_2046238) baseStart_2046238 baseEnd_2046238 := by
    simpa [prefixWord, tailWord_2046238, baseEnd_2046238] using wordTrace_append hprefix tailTrace_2046238
  have hstable : (prefixWord ++ tailWord_2046238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046238).length < 2 ^ (prefixWord ++ tailWord_2046238).sum := by decide
  have hdescent : baseEnd_2046238 < baseStart_2046238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046252 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_2046252 : Nat := 118140960795 + 2046252 * 2 ^ 59
def prefixEnd_2046252 : Nat := 4983230072969 + 3 ^ 40 * 2046252 * 2
def baseEnd_2046252 : Nat := 466982584988459228150873

theorem tailTrace_2046252 : CollatzResearch.WordTrace tailWord_2046252 prefixEnd_2046252 466982584988459228150873 := by
  unfold tailWord_2046252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37316470891392975431910505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49755294521857300575880673 37316470891392975431910505)
  ·
    refine ⟨27987353168544731573932879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37316470891392975431910505 27987353168544731573932879)
    ·
      refine ⟨41981029752817097360899319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27987353168544731573932879 41981029752817097360899319)
      ·
        refine ⟨62971544629225646041348979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41981029752817097360899319 62971544629225646041348979)
        ·
          refine ⟨94457316943838469062023469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62971544629225646041348979 94457316943838469062023469)
          ·
            refine ⟨35421493853939425898258801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94457316943838469062023469 35421493853939425898258801)
            ·
              refine ⟨26566120390454569423694101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35421493853939425898258801 26566120390454569423694101)
              ·
                refine ⟨1245286893302557941735661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26566120390454569423694101 1245286893302557941735661)
                ·
                  refine ⟨466982584988459228150873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245286893302557941735661 466982584988459228150873)
                  ·
                    rfl

theorem cell21_2046252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_2046252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046252 prefixEnd_2046252 := by exact prefixLift 2046252
  have htrace : WordTrace (prefixWord ++ tailWord_2046252) baseStart_2046252 baseEnd_2046252 := by
    simpa [prefixWord, tailWord_2046252, baseEnd_2046252] using wordTrace_append hprefix tailTrace_2046252
  have hstable : (prefixWord ++ tailWord_2046252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046252).length < 2 ^ (prefixWord ++ tailWord_2046252).sum := by decide
  have hdescent : baseEnd_2046252 < baseStart_2046252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046280 : List Nat := [2, 1, 3, 1, 1, 2, 4, 7]
def baseStart_2046280 : Nat := 118140960795 + 2046280 * 2 ^ 59
def prefixEnd_2046280 : Nat := 4983230072969 + 3 ^ 40 * 2046280 * 2
def baseEnd_2046280 : Nat := 155662991656645800561383

theorem tailTrace_2046280 : CollatzResearch.WordTrace tailWord_2046280 prefixEnd_2046280 155662991656645800561383 := by
  unfold tailWord_2046280
  simp only [CollatzResearch.WordTrace]
  refine ⟨37316981513342255822920147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49755975351123007763893529 37316981513342255822920147)
  ·
    refine ⟨55975472270013383734380221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37316981513342255822920147 55975472270013383734380221)
    ·
      refine ⟨20990802101255018900392583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55975472270013383734380221 20990802101255018900392583)
      ·
        refine ⟨31486203151882528350588875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20990802101255018900392583 31486203151882528350588875)
        ·
          refine ⟨47229304727823792525883313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31486203151882528350588875 47229304727823792525883313)
          ·
            refine ⟨35421978545867844394412485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47229304727823792525883313 35421978545867844394412485)
            ·
              refine ⟨6641620977350220823952341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35421978545867844394412485 6641620977350220823952341)
              ·
                refine ⟨155662991656645800561383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6641620977350220823952341 155662991656645800561383)
                ·
                  rfl

theorem cell21_2046280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_2046280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046280 prefixEnd_2046280 := by exact prefixLift 2046280
  have htrace : WordTrace (prefixWord ++ tailWord_2046280) baseStart_2046280 baseEnd_2046280 := by
    simpa [prefixWord, tailWord_2046280, baseEnd_2046280] using wordTrace_append hprefix tailTrace_2046280
  have hstable : (prefixWord ++ tailWord_2046280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046280).length < 2 ^ (prefixWord ++ tailWord_2046280).sum := by decide
  have hdescent : baseEnd_2046280 < baseStart_2046280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046314 : List Nat := [3, 1, 3, 3, 1, 3, 1, 6]
def baseStart_2046314 : Nat := 118140960795 + 2046314 * 2 ^ 59
def prefixEnd_2046314 : Nat := 4983230072969 + 3 ^ 40 * 2046314 * 2
def baseEnd_2046314 : Nat := 155665578077720299372471

theorem tailTrace_2046314 : CollatzResearch.WordTrace tailWord_2046314 prefixEnd_2046314 155665578077720299372471 := by
  unfold tailWord_2046314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18658800777140333863144499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49756802072374223635051997 18658800777140333863144499)
  ·
    refine ⟨27988201165710500794716749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18658800777140333863144499 27988201165710500794716749)
    ·
      refine ⟨10495575437141437798018781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27988201165710500794716749 10495575437141437798018781)
      ·
        refine ⟨3935840788928039174257043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10495575437141437798018781 3935840788928039174257043)
        ·
          refine ⟨5903761183392058761385565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935840788928039174257043 5903761183392058761385565)
          ·
            refine ⟨2213910443772022035519587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5903761183392058761385565 2213910443772022035519587)
            ·
              refine ⟨3320865665658033053279381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213910443772022035519587 3320865665658033053279381)
              ·
                refine ⟨155665578077720299372471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3320865665658033053279381 155665578077720299372471)
                ·
                  rfl

theorem cell21_2046314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_2046314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046314 prefixEnd_2046314 := by exact prefixLift 2046314
  have htrace : WordTrace (prefixWord ++ tailWord_2046314) baseStart_2046314 baseEnd_2046314 := by
    simpa [prefixWord, tailWord_2046314, baseEnd_2046314] using wordTrace_append hprefix tailTrace_2046314
  have hstable : (prefixWord ++ tailWord_2046314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046314).length < 2 ^ (prefixWord ++ tailWord_2046314).sum := by decide
  have hdescent : baseEnd_2046314 < baseStart_2046314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046345 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 3]
def baseStart_2046345 : Nat := 118140960795 + 2046345 * 2 ^ 59
def prefixEnd_2046345 : Nat := 4983230072969 + 3 ^ 40 * 2046345 * 2
def baseEnd_2046345 : Nat := 467003808855511733100683

theorem tailTrace_2046345 : CollatzResearch.WordTrace tailWord_2046345 prefixEnd_2046345 467003808855511733100683 := by
  unfold tailWord_2046345
  simp only [CollatzResearch.WordTrace]
  refine ⟨74636333771449027746956489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49757555847632685164637659 74636333771449027746956489)
  ·
    refine ⟨55977250328586770810217367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74636333771449027746956489 55977250328586770810217367)
    ·
      refine ⟨83965875492880156215326051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55977250328586770810217367 83965875492880156215326051)
      ·
        refine ⟨125948813239320234322989077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83965875492880156215326051 125948813239320234322989077)
        ·
          refine ⟨5903850620593135983890113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125948813239320234322989077 5903850620593135983890113)
          ·
            refine ⟨4427887965444851987917585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5903850620593135983890113 4427887965444851987917585)
            ·
              refine ⟨3320915974083638990938189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427887965444851987917585 3320915974083638990938189)
              ·
                refine ⟨1245343490281364621601821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320915974083638990938189 1245343490281364621601821)
                ·
                  refine ⟨467003808855511733100683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245343490281364621601821 467003808855511733100683)
                  ·
                    rfl

theorem cell21_2046345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_2046345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046345 prefixEnd_2046345 := by exact prefixLift 2046345
  have htrace : WordTrace (prefixWord ++ tailWord_2046345) baseStart_2046345 baseEnd_2046345 := by
    simpa [prefixWord, tailWord_2046345, baseEnd_2046345] using wordTrace_append hprefix tailTrace_2046345
  have hstable : (prefixWord ++ tailWord_2046345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046345).length < 2 ^ (prefixWord ++ tailWord_2046345).sum := by decide
  have hdescent : baseEnd_2046345 < baseStart_2046345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046432 : List Nat := [2, 1, 1, 3, 1, 1, 6, 6]
def baseStart_2046432 : Nat := 118140960795 + 2046432 * 2 ^ 59
def prefixEnd_2046432 : Nat := 4983230072969 + 3 ^ 40 * 2046432 * 2
def baseEnd_2046432 : Nat := 155674554480272971716835

theorem tailTrace_2046432 : CollatzResearch.WordTrace tailWord_2046432 prefixEnd_2046432 155674554480272971716835 := by
  unfold tailWord_2046432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319753461066920802686775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49759671281422561070249033 37319753461066920802686775)
  ·
    refine ⟨55979630191600381204030163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319753461066920802686775 55979630191600381204030163)
    ·
      refine ⟨83969445287400571806045245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55979630191600381204030163 83969445287400571806045245)
      ·
        refine ⟨31488541982775214427266967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83969445287400571806045245 31488541982775214427266967)
        ·
          refine ⟨47232812974162821640900451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31488541982775214427266967 47232812974162821640900451)
          ·
            refine ⟨70849219461244232461350677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47232812974162821640900451 70849219461244232461350677)
            ·
              refine ⟨3321057162245823396625813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70849219461244232461350677 3321057162245823396625813)
              ·
                refine ⟨155674554480272971716835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3321057162245823396625813 155674554480272971716835)
                ·
                  rfl

theorem cell21_2046432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_2046432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046432 prefixEnd_2046432 := by exact prefixLift 2046432
  have htrace : WordTrace (prefixWord ++ tailWord_2046432) baseStart_2046432 baseEnd_2046432 := by
    simpa [prefixWord, tailWord_2046432, baseEnd_2046432] using wordTrace_append hprefix tailTrace_2046432
  have hstable : (prefixWord ++ tailWord_2046432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046432).length < 2 ^ (prefixWord ++ tailWord_2046432).sum := by decide
  have hdescent : baseEnd_2046432 < baseStart_2046432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046435 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_2046435 : Nat := 118140960795 + 2046435 * 2 ^ 59
def prefixEnd_2046435 : Nat := 4983230072969 + 3 ^ 40 * 2046435 * 2
def baseEnd_2046435 : Nat := 467024348081691576600499

theorem tailTrace_2046435 : CollatzResearch.WordTrace tailWord_2046435 prefixEnd_2046435 467024348081691576600499 := by
  unfold tailWord_2046435
  simp only [CollatzResearch.WordTrace]
  refine ⟨74639616341122973117732759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49759744227415315411821839 74639616341122973117732759)
  ·
    refine ⟨111959424511684459676599139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74639616341122973117732759 111959424511684459676599139)
    ·
      refine ⟨167939136767526689514898709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111959424511684459676599139 167939136767526689514898709)
      ·
        refine ⟨7872147035977813571010877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167939136767526689514898709 7872147035977813571010877)
        ·
          refine ⟨2952055138491680089129079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7872147035977813571010877 2952055138491680089129079)
          ·
            refine ⟨4428082707737520133693619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952055138491680089129079 4428082707737520133693619)
            ·
              refine ⟨6642124061606280200540429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428082707737520133693619 6642124061606280200540429)
              ·
                refine ⟨2490796523102355075202661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6642124061606280200540429 2490796523102355075202661)
                ·
                  refine ⟨467024348081691576600499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2490796523102355075202661 467024348081691576600499)
                  ·
                    rfl

theorem cell21_2046435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_2046435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046435 prefixEnd_2046435 := by exact prefixLift 2046435
  have htrace : WordTrace (prefixWord ++ tailWord_2046435) baseStart_2046435 baseEnd_2046435 := by
    simpa [prefixWord, tailWord_2046435, baseEnd_2046435] using wordTrace_append hprefix tailTrace_2046435
  have hstable : (prefixWord ++ tailWord_2046435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046435).length < 2 ^ (prefixWord ++ tailWord_2046435).sum := by decide
  have hdescent : baseEnd_2046435 < baseStart_2046435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046466 : List Nat := [3, 4, 1, 2, 3, 8]
def baseStart_2046466 : Nat := 118140960795 + 2046466 * 2 ^ 59
def prefixEnd_2046466 : Nat := 4983230072969 + 3 ^ 40 * 2046466 * 2
def baseEnd_2046466 : Nat := 17297460100149718947547

theorem tailTrace_2046466 : CollatzResearch.WordTrace tailWord_2046466 prefixEnd_2046466 17297460100149718947547 := by
  unfold tailWord_2046466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18660186751002666353027813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49760498002673776941407501 18660186751002666353027813)
  ·
    refine ⟨3498785015812999941192715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18660186751002666353027813 3498785015812999941192715)
    ·
      refine ⟨5248177523719499911789073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498785015812999941192715 5248177523719499911789073)
      ·
        refine ⟨3936133142789624933841805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5248177523719499911789073 3936133142789624933841805)
        ·
          refine ⟨1476049928546109350190677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3936133142789624933841805 1476049928546109350190677)
          ·
            refine ⟨17297460100149718947547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1476049928546109350190677 17297460100149718947547)
            ·
              rfl

theorem cell21_2046466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 8].length) (baseStart_2046466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046466 prefixEnd_2046466 := by exact prefixLift 2046466
  have htrace : WordTrace (prefixWord ++ tailWord_2046466) baseStart_2046466 baseEnd_2046466 := by
    simpa [prefixWord, tailWord_2046466, baseEnd_2046466] using wordTrace_append hprefix tailTrace_2046466
  have hstable : (prefixWord ++ tailWord_2046466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046466).length < 2 ^ (prefixWord ++ tailWord_2046466).sum := by decide
  have hdescent : baseEnd_2046466 < baseStart_2046466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046573 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2046573 : Nat := 118140960795 + 2046573 * 2 ^ 59
def prefixEnd_2046573 : Nat := 4983230072969 + 3 ^ 40 * 2046573 * 2
def baseEnd_2046573 : Nat := 467055841561834003300217

theorem tailTrace_2046573 : CollatzResearch.WordTrace tailWord_2046573 prefixEnd_2046573 467055841561834003300217 := by
  unfold tailWord_2046573
  simp only [CollatzResearch.WordTrace]
  refine ⟨74644649614623022686256373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49763099743082015124170915 74644649614623022686256373)
  ·
    refine ⟨6997935901370908376836535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74644649614623022686256373 6997935901370908376836535)
    ·
      refine ⟨10496903852056362565254803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6997935901370908376836535 10496903852056362565254803)
      ·
        refine ⟨15745355778084543847882205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10496903852056362565254803 15745355778084543847882205)
        ·
          refine ⟨5904508416781703942955827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15745355778084543847882205 5904508416781703942955827)
          ·
            refine ⟨8856762625172555914433741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5904508416781703942955827 8856762625172555914433741)
            ·
              refine ⟨3321285984439708467912653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8856762625172555914433741 3321285984439708467912653)
              ·
                refine ⟨1245482244164890675467245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321285984439708467912653 1245482244164890675467245)
                ·
                  refine ⟨467055841561834003300217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245482244164890675467245 467055841561834003300217)
                  ·
                    rfl

theorem cell21_2046573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2046573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046573 prefixEnd_2046573 := by exact prefixLift 2046573
  have htrace : WordTrace (prefixWord ++ tailWord_2046573) baseStart_2046573 baseEnd_2046573 := by
    simpa [prefixWord, tailWord_2046573, baseEnd_2046573] using wordTrace_append hprefix tailTrace_2046573
  have hstable : (prefixWord ++ tailWord_2046573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046573).length < 2 ^ (prefixWord ++ tailWord_2046573).sum := by decide
  have hdescent : baseEnd_2046573 < baseStart_2046573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046643 : List Nat := [1, 1, 1, 2, 3, 13]
def baseStart_2046643 : Nat := 118140960795 + 2046643 * 2 ^ 59
def prefixEnd_2046643 : Nat := 4983230072969 + 3 ^ 40 * 2046643 * 2
def baseEnd_2046643 : Nat := 17298956167241831004941

theorem tailTrace_2046643 : CollatzResearch.WordTrace tailWord_2046643 prefixEnd_2046643 17298956167241831004941 := by
  unfold tailWord_2046643
  simp only [CollatzResearch.WordTrace]
  refine ⟨74647202724369424641304583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49764801816246283094203055 74647202724369424641304583)
  ·
    refine ⟨111970804086554136961956875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74647202724369424641304583 111970804086554136961956875)
    ·
      refine ⟨167956206129831205442935313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111970804086554136961956875 167956206129831205442935313)
      ·
        refine ⟨125967154597373404082201485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167956206129831205442935313 125967154597373404082201485)
        ·
          refine ⟨47237682974015026530825557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125967154597373404082201485 47237682974015026530825557)
          ·
            refine ⟨17298956167241831004941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 47237682974015026530825557 17298956167241831004941)
            ·
              rfl

theorem cell21_2046643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 13].length) (baseStart_2046643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046643 prefixEnd_2046643 := by exact prefixLift 2046643
  have htrace : WordTrace (prefixWord ++ tailWord_2046643) baseStart_2046643 baseEnd_2046643 := by
    simpa [prefixWord, tailWord_2046643, baseEnd_2046643] using wordTrace_append hprefix tailTrace_2046643
  have hstable : (prefixWord ++ tailWord_2046643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046643).length < 2 ^ (prefixWord ++ tailWord_2046643).sum := by decide
  have hdescent : baseEnd_2046643 < baseStart_2046643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046705 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2046705 : Nat := 118140960795 + 2046705 * 2 ^ 59
def prefixEnd_2046705 : Nat := 4983230072969 + 3 ^ 40 * 2046705 * 2
def baseEnd_2046705 : Nat := 467085965760231107099947

theorem tailTrace_2046705 : CollatzResearch.WordTrace tailWord_2046705 prefixEnd_2046705 467085965760231107099947 := by
  unfold tailWord_2046705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74649464050144809230061569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49766309366763206153374379 74649464050144809230061569)
  ·
    refine ⟨55987098037608606922546177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74649464050144809230061569 55987098037608606922546177)
    ·
      refine ⟨41990323528206455191909633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55987098037608606922546177 41990323528206455191909633)
      ·
        refine ⟨31492742646154841393932225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41990323528206455191909633 31492742646154841393932225)
        ·
          refine ⟨23619556984616131045449169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31492742646154841393932225 23619556984616131045449169)
          ·
            refine ⟨17714667738462098284086877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23619556984616131045449169 17714667738462098284086877)
            ·
              refine ⟨6643000401923286856532579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17714667738462098284086877 6643000401923286856532579)
              ·
                refine ⟨9964500602884930284798869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643000401923286856532579 9964500602884930284798869)
                ·
                  refine ⟨467085965760231107099947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9964500602884930284798869 467085965760231107099947)
                  ·
                    rfl

theorem cell21_2046705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2046705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046705 prefixEnd_2046705 := by exact prefixLift 2046705
  have htrace : WordTrace (prefixWord ++ tailWord_2046705) baseStart_2046705 baseEnd_2046705 := by
    simpa [prefixWord, tailWord_2046705, baseEnd_2046705] using wordTrace_append hprefix tailTrace_2046705
  have hstable : (prefixWord ++ tailWord_2046705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046705).length < 2 ^ (prefixWord ++ tailWord_2046705).sum := by decide
  have hdescent : baseEnd_2046705 < baseStart_2046705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046719 : List Nat := [1, 1, 2, 2, 1, 3, 1, 10]
def baseStart_2046719 : Nat := 118140960795 + 2046719 * 2 ^ 59
def prefixEnd_2046719 : Nat := 4983230072969 + 3 ^ 40 * 2046719 * 2
def baseEnd_2046719 : Nat := 155696386916990064622195

theorem tailTrace_2046719 : CollatzResearch.WordTrace tailWord_2046719 prefixEnd_2046719 155696386916990064622195 := by
  unfold tailWord_2046719
  simp only [CollatzResearch.WordTrace]
  refine ⟨74649974672094089621071211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49766649781396059747380807 74649974672094089621071211)
  ·
    refine ⟨111974962008141134431606817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74649974672094089621071211 111974962008141134431606817)
    ·
      refine ⟨83981221506105850823705113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111974962008141134431606817 83981221506105850823705113)
      ·
        refine ⟨62985916129579388117778835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83981221506105850823705113 62985916129579388117778835)
        ·
          refine ⟨94478874194369082176668253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62985916129579388117778835 94478874194369082176668253)
          ·
            refine ⟨35429577822888405816250595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94478874194369082176668253 35429577822888405816250595)
            ·
              refine ⟨53144366734332608724375893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35429577822888405816250595 53144366734332608724375893)
              ·
                refine ⟨155696386916990064622195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53144366734332608724375893 155696386916990064622195)
                ·
                  rfl

theorem cell21_2046719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_2046719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046719 prefixEnd_2046719 := by exact prefixLift 2046719
  have htrace : WordTrace (prefixWord ++ tailWord_2046719) baseStart_2046719 baseEnd_2046719 := by
    simpa [prefixWord, tailWord_2046719, baseEnd_2046719] using wordTrace_append hprefix tailTrace_2046719
  have hstable : (prefixWord ++ tailWord_2046719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046719).length < 2 ^ (prefixWord ++ tailWord_2046719).sum := by decide
  have hdescent : baseEnd_2046719 < baseStart_2046719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046812 : List Nat := [2, 2, 4, 2, 1, 10]
def baseStart_2046812 : Nat := 118140960795 + 2046812 * 2 ^ 59
def prefixEnd_2046812 : Nat := 4983230072969 + 3 ^ 40 * 2046812 * 2
def baseEnd_2046812 : Nat := 17300384615482322178385

theorem tailTrace_2046812 : CollatzResearch.WordTrace tailWord_2046812 prefixEnd_2046812 17300384615482322178385 := by
  unfold tailWord_2046812
  simp only [CollatzResearch.WordTrace]
  refine ⟨37326683330378583252103345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49768911107171444336137793 37326683330378583252103345)
  ·
    refine ⟨27995012497783937439077509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37326683330378583252103345 27995012497783937439077509)
    ·
      refine ⟨5249064843334488269827033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27995012497783937439077509 5249064843334488269827033)
      ·
        refine ⟨3936798632500866202370275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5249064843334488269827033 3936798632500866202370275)
        ·
          refine ⟨5905197948751299303555413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3936798632500866202370275 5905197948751299303555413)
          ·
            refine ⟨17300384615482322178385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5905197948751299303555413 17300384615482322178385)
            ·
              rfl

theorem cell21_2046812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 10].length) (baseStart_2046812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046812 prefixEnd_2046812 := by exact prefixLift 2046812
  have htrace : WordTrace (prefixWord ++ tailWord_2046812) baseStart_2046812 baseEnd_2046812 := by
    simpa [prefixWord, tailWord_2046812, baseEnd_2046812] using wordTrace_append hprefix tailTrace_2046812
  have hstable : (prefixWord ++ tailWord_2046812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046812).length < 2 ^ (prefixWord ++ tailWord_2046812).sum := by decide
  have hdescent : baseEnd_2046812 < baseStart_2046812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046871 : List Nat := [1, 1, 3, 3, 1, 2, 10]
def baseStart_2046871 : Nat := 118140960795 + 2046871 * 2 ^ 59
def prefixEnd_2046871 : Nat := 4983230072969 + 3 ^ 40 * 2046871 * 2
def baseEnd_2046871 : Nat := 51902649913539078592549

theorem tailTrace_2046871 : CollatzResearch.WordTrace tailWord_2046871 prefixEnd_2046871 51902649913539078592549 := by
  unfold tailWord_2046871
  simp only [CollatzResearch.WordTrace]
  refine ⟨74655518567543419580604467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49770345711695613053736311 74655518567543419580604467)
  ·
    refine ⟨111983277851315129370906701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74655518567543419580604467 111983277851315129370906701)
    ·
      refine ⟨41993729194243173514090013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111983277851315129370906701 41993729194243173514090013)
      ·
        refine ⟨15747648447841190067783755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41993729194243173514090013 15747648447841190067783755)
        ·
          refine ⟨23621472671761785101675633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747648447841190067783755 23621472671761785101675633)
          ·
            refine ⟨17716104503821338826256725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23621472671761785101675633 17716104503821338826256725)
            ·
              refine ⟨51902649913539078592549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17716104503821338826256725 51902649913539078592549)
              ·
                rfl

theorem cell21_2046871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 10].length) (baseStart_2046871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046871 prefixEnd_2046871 := by exact prefixLift 2046871
  have htrace : WordTrace (prefixWord ++ tailWord_2046871) baseStart_2046871 baseEnd_2046871 := by
    simpa [prefixWord, tailWord_2046871, baseEnd_2046871] using wordTrace_append hprefix tailTrace_2046871
  have hstable : (prefixWord ++ tailWord_2046871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046871).length < 2 ^ (prefixWord ++ tailWord_2046871).sum := by decide
  have hdescent : baseEnd_2046871 < baseStart_2046871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046874 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_2046874 : Nat := 118140960795 + 2046874 * 2 ^ 59
def prefixEnd_2046874 : Nat := 4983230072969 + 3 ^ 40 * 2046874 * 2
def baseEnd_2046874 : Nat := 467124533862724368782935

theorem tailTrace_2046874 : CollatzResearch.WordTrace tailWord_2046874 prefixEnd_2046874 467124533862724368782935 := by
  unfold tailWord_2046874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663906996633137773240919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49770418657688367395309117 18663906996633137773240919)
  ·
    refine ⟨27995860494949706659861379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663906996633137773240919 27995860494949706659861379)
    ·
      refine ⟨41993790742424559989792069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27995860494949706659861379 41993790742424559989792069)
      ·
        refine ⟨7873835764204604998086013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41993790742424559989792069 7873835764204604998086013)
        ·
          refine ⟨2952688411576726874282255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7873835764204604998086013 2952688411576726874282255)
          ·
            refine ⟨4429032617365090311423383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952688411576726874282255 4429032617365090311423383)
            ·
              refine ⟨6643548926047635467135075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429032617365090311423383 6643548926047635467135075)
              ·
                refine ⟨9965323389071453200702613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643548926047635467135075 9965323389071453200702613)
                ·
                  refine ⟨467124533862724368782935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9965323389071453200702613 467124533862724368782935)
                  ·
                    rfl

theorem cell21_2046874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_2046874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046874 prefixEnd_2046874 := by exact prefixLift 2046874
  have htrace : WordTrace (prefixWord ++ tailWord_2046874) baseStart_2046874 baseEnd_2046874 := by
    simpa [prefixWord, tailWord_2046874, baseEnd_2046874] using wordTrace_append hprefix tailTrace_2046874
  have hstable : (prefixWord ++ tailWord_2046874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046874).length < 2 ^ (prefixWord ++ tailWord_2046874).sum := by decide
  have hdescent : baseEnd_2046874 < baseStart_2046874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046905 : List Nat := [1, 2, 1, 4, 2, 4, 2, 5]
def baseStart_2046905 : Nat := 118140960795 + 2046905 * 2 ^ 59
def prefixEnd_2046905 : Nat := 4983230072969 + 3 ^ 40 * 2046905 * 2
def baseEnd_2046905 : Nat := 155710536161691734588735

theorem tailTrace_2046905 : CollatzResearch.WordTrace tailWord_2046905 prefixEnd_2046905 155710536161691734588735 := by
  unfold tailWord_2046905
  simp only [CollatzResearch.WordTrace]
  refine ⟨74656758649420243387342169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49771172432946828924894779 74656758649420243387342169)
  ·
    refine ⟨55992568987065182540506627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74656758649420243387342169 55992568987065182540506627)
    ·
      refine ⟨83988853480597773810759941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55992568987065182540506627 83988853480597773810759941)
      ·
        refine ⟨15747910027612082589517489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83988853480597773810759941 15747910027612082589517489)
        ·
          refine ⟨11810932520709061942138117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15747910027612082589517489 11810932520709061942138117)
          ·
            refine ⟨2214549847632949114150897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11810932520709061942138117 2214549847632949114150897)
            ·
              refine ⟨1660912385724711835613173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214549847632949114150897 1660912385724711835613173)
              ·
                refine ⟨155710536161691734588735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1660912385724711835613173 155710536161691734588735)
                ·
                  rfl

theorem cell21_2046905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 5].length) (baseStart_2046905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2046905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2046905 prefixEnd_2046905 := by exact prefixLift 2046905
  have htrace : WordTrace (prefixWord ++ tailWord_2046905) baseStart_2046905 baseEnd_2046905 := by
    simpa [prefixWord, tailWord_2046905, baseEnd_2046905] using wordTrace_append hprefix tailTrace_2046905
  have hstable : (prefixWord ++ tailWord_2046905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046905).length < 2 ^ (prefixWord ++ tailWord_2046905).sum := by decide
  have hdescent : baseEnd_2046905 < baseStart_2046905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047074 : List Nat := [3, 3, 2, 2, 1, 3, 2, 5]
def baseStart_2047074 : Nat := 118140960795 + 2047074 * 2 ^ 59
def prefixEnd_2047074 : Nat := 4983230072969 + 3 ^ 40 * 2047074 * 2
def baseEnd_2047074 : Nat := 155723392195856155149731

theorem tailTrace_2047074 : CollatzResearch.WordTrace tailWord_2047074 prefixEnd_2047074 155723392195856155149731 := by
  unfold tailWord_2047074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18665730646451996312561069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49775281723871990166829517 18665730646451996312561069)
  ·
    refine ⟨6999648992419498617210401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18665730646451996312561069 6999648992419498617210401)
    ·
      refine ⟨5249736744314623962907801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6999648992419498617210401 5249736744314623962907801)
      ·
        refine ⟨3937302558235967972180851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5249736744314623962907801 3937302558235967972180851)
        ·
          refine ⟨5905953837353951958271277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3937302558235967972180851 5905953837353951958271277)
          ·
            refine ⟨2214732689007731984351729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5905953837353951958271277 2214732689007731984351729)
            ·
              refine ⟨1661049516755798988263797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214732689007731984351729 1661049516755798988263797)
              ·
                refine ⟨155723392195856155149731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661049516755798988263797 155723392195856155149731)
                ·
                  rfl

theorem cell21_2047074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_2047074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047074 prefixEnd_2047074 := by exact prefixLift 2047074
  have htrace : WordTrace (prefixWord ++ tailWord_2047074) baseStart_2047074 baseEnd_2047074 := by
    simpa [prefixWord, tailWord_2047074, baseEnd_2047074] using wordTrace_append hprefix tailTrace_2047074
  have hstable : (prefixWord ++ tailWord_2047074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047074).length < 2 ^ (prefixWord ++ tailWord_2047074).sum := by decide
  have hdescent : baseEnd_2047074 < baseStart_2047074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047085 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2047085 : Nat := 118140960795 + 2047085 * 2 ^ 59
def prefixEnd_2047085 : Nat := 4983230072969 + 3 ^ 40 * 2047085 * 2
def baseEnd_2047085 : Nat := 467172686937434890765837

theorem tailTrace_2047085 : CollatzResearch.WordTrace tailWord_2047085 prefixEnd_2047085 467172686937434890765837 := by
  unfold tailWord_2047085
  simp only [CollatzResearch.WordTrace]
  refine ⟨74663323788768134128894709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49775549192512089419263139 74663323788768134128894709)
  ·
    refine ⟨6999686605197012574583879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74663323788768134128894709 6999686605197012574583879)
    ·
      refine ⟨10499529907795518861875819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6999686605197012574583879 10499529907795518861875819)
      ·
        refine ⟨15749294861693278292813729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10499529907795518861875819 15749294861693278292813729)
        ·
          refine ⟨11811971146269958719610297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15749294861693278292813729 11811971146269958719610297)
          ·
            refine ⟨8858978359702469039707723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11811971146269958719610297 8858978359702469039707723)
            ·
              refine ⟨13288467539553703559561585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858978359702469039707723 13288467539553703559561585)
              ·
                refine ⟨9966350654665277669671189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288467539553703559561585 9966350654665277669671189)
                ·
                  refine ⟨467172686937434890765837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9966350654665277669671189 467172686937434890765837)
                  ·
                    rfl

theorem cell21_2047085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2047085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047085 prefixEnd_2047085 := by exact prefixLift 2047085
  have htrace : WordTrace (prefixWord ++ tailWord_2047085) baseStart_2047085 baseEnd_2047085 := by
    simpa [prefixWord, tailWord_2047085, baseEnd_2047085] using wordTrace_append hprefix tailTrace_2047085
  have hstable : (prefixWord ++ tailWord_2047085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047085).length < 2 ^ (prefixWord ++ tailWord_2047085).sum := by decide
  have hdescent : baseEnd_2047085 < baseStart_2047085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047105 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 3]
def baseStart_2047105 : Nat := 118140960795 + 2047105 * 2 ^ 59
def prefixEnd_2047105 : Nat := 4983230072969 + 3 ^ 40 * 2047105 * 2
def baseEnd_2047105 : Nat := 467177251209919300432463

theorem tailTrace_2047105 : CollatzResearch.WordTrace tailWord_2047105 prefixEnd_2047105 467177251209919300432463 := by
  unfold tailWord_2047105
  simp only [CollatzResearch.WordTrace]
  refine ⟨74664053248695677544622769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49776035499130451696415179 74664053248695677544622769)
  ·
    refine ⟨55998039936521758158467077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74664053248695677544622769 55998039936521758158467077)
    ·
      refine ⟨10499632488097829654712577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55998039936521758158467077 10499632488097829654712577)
      ·
        refine ⟨7874724366073372241034433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10499632488097829654712577 7874724366073372241034433)
        ·
          refine ⟨5906043274555029180775825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7874724366073372241034433 5906043274555029180775825)
          ·
            refine ⟨4429532455916271885581869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906043274555029180775825 4429532455916271885581869)
            ·
              refine ⟨1661074670968601957093201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4429532455916271885581869 1661074670968601957093201)
              ·
                refine ⟨1245806003226451467819901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661074670968601957093201 1245806003226451467819901)
                ·
                  refine ⟨467177251209919300432463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245806003226451467819901 467177251209919300432463)
                  ·
                    rfl

theorem cell21_2047105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_2047105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047105 prefixEnd_2047105 := by exact prefixLift 2047105
  have htrace : WordTrace (prefixWord ++ tailWord_2047105) baseStart_2047105 baseEnd_2047105 := by
    simpa [prefixWord, tailWord_2047105, baseEnd_2047105] using wordTrace_append hprefix tailTrace_2047105
  have hstable : (prefixWord ++ tailWord_2047105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047105).length < 2 ^ (prefixWord ++ tailWord_2047105).sum := by decide
  have hdescent : baseEnd_2047105 < baseStart_2047105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047161 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_2047161 : Nat := 118140960795 + 2047161 * 2 ^ 59
def prefixEnd_2047161 : Nat := 4983230072969 + 3 ^ 40 * 2047161 * 2
def baseEnd_2047161 : Nat := 467190031172875647499015

theorem tailTrace_2047161 : CollatzResearch.WordTrace tailWord_2047161 prefixEnd_2047161 467190031172875647499015 := by
  unfold tailWord_2047161
  simp only [CollatzResearch.WordTrace]
  refine ⟨74666095736492799108661337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49777397157661866072440891 74666095736492799108661337)
  ·
    refine ⟨55999571802369599331496003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74666095736492799108661337 55999571802369599331496003)
    ·
      refine ⟨83999357703554398997244005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55999571802369599331496003 83999357703554398997244005)
      ·
        refine ⟨15749879569416449811983251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83999357703554398997244005 15749879569416449811983251)
        ·
          refine ⟨23624819354124674717974877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15749879569416449811983251 23624819354124674717974877)
          ·
            refine ⟨8859307257796753019240579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23624819354124674717974877 8859307257796753019240579)
            ·
              refine ⟨13288960886695129528860869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859307257796753019240579 13288960886695129528860869)
              ·
                refine ⟨2491680166255336786661413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13288960886695129528860869 2491680166255336786661413)
                ·
                  refine ⟨467190031172875647499015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491680166255336786661413 467190031172875647499015)
                  ·
                    rfl

theorem cell21_2047161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_2047161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047161 prefixEnd_2047161 := by exact prefixLift 2047161
  have htrace : WordTrace (prefixWord ++ tailWord_2047161) baseStart_2047161 baseEnd_2047161 := by
    simpa [prefixWord, tailWord_2047161, baseEnd_2047161] using wordTrace_append hprefix tailTrace_2047161
  have hstable : (prefixWord ++ tailWord_2047161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047161).length < 2 ^ (prefixWord ++ tailWord_2047161).sum := by decide
  have hdescent : baseEnd_2047161 < baseStart_2047161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047164 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_2047164 : Nat := 118140960795 + 2047164 * 2 ^ 59
def prefixEnd_2047164 : Nat := 4983230072969 + 3 ^ 40 * 2047164 * 2
def baseEnd_2047164 : Nat := 467190715813748308949009

theorem tailTrace_2047164 : CollatzResearch.WordTrace tailWord_2047164 prefixEnd_2047164 467190715813748308949009 := by
  unfold tailWord_2047164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37333102577740965310510273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49777470103654620414013697 37333102577740965310510273)
  ·
    refine ⟨27999826933305723982882705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37333102577740965310510273 27999826933305723982882705)
    ·
      refine ⟨20999870199979292987162029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27999826933305723982882705 20999870199979292987162029)
      ·
        refine ⟨7874951324992234870185761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20999870199979292987162029 7874951324992234870185761)
        ·
          refine ⟨5906213493744176152639321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7874951324992234870185761 5906213493744176152639321)
          ·
            refine ⟨4429660120308132114479491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906213493744176152639321 4429660120308132114479491)
            ·
              refine ⟨6644490180462198171719237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429660120308132114479491 6644490180462198171719237)
              ·
                refine ⟨1245841908836662157197357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6644490180462198171719237 1245841908836662157197357)
                ·
                  refine ⟨467190715813748308949009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1245841908836662157197357 467190715813748308949009)
                  ·
                    rfl

theorem cell21_2047164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_2047164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047164 prefixEnd_2047164 := by exact prefixLift 2047164
  have htrace : WordTrace (prefixWord ++ tailWord_2047164) baseStart_2047164 baseEnd_2047164 := by
    simpa [prefixWord, tailWord_2047164, baseEnd_2047164] using wordTrace_append hprefix tailTrace_2047164
  have hstable : (prefixWord ++ tailWord_2047164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047164).length < 2 ^ (prefixWord ++ tailWord_2047164).sum := by decide
  have hdescent : baseEnd_2047164 < baseStart_2047164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047181 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2047181 : Nat := 118140960795 + 2047181 * 2 ^ 59
def prefixEnd_2047181 : Nat := 4983230072969 + 3 ^ 40 * 2047181 * 2
def baseEnd_2047181 : Nat := 467194595445360057165641

theorem tailTrace_2047181 : CollatzResearch.WordTrace tailWord_2047181 prefixEnd_2047181 467194595445360057165641 := by
  unfold tailWord_2047181
  simp only [CollatzResearch.WordTrace]
  refine ⟨74666825196420342524389397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49777883464280228349592931 74666825196420342524389397)
  ·
    refine ⟨3500007431082203555830753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74666825196420342524389397 3500007431082203555830753)
    ·
      refine ⟨2625005573311652666873065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500007431082203555830753 2625005573311652666873065)
      ·
        refine ⟨1968754179983739500154799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2625005573311652666873065 1968754179983739500154799)
        ·
          refine ⟨2953131269975609250232199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968754179983739500154799 2953131269975609250232199)
          ·
            refine ⟨4429696904963413875348299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953131269975609250232199 4429696904963413875348299)
            ·
              refine ⟨6644545357445120813022449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4429696904963413875348299 6644545357445120813022449)
              ·
                refine ⟨4983409018083840609766837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644545357445120813022449 4983409018083840609766837)
                ·
                  refine ⟨467194595445360057165641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4983409018083840609766837 467194595445360057165641)
                  ·
                    rfl

theorem cell21_2047181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2047181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047181 prefixEnd_2047181 := by exact prefixLift 2047181
  have htrace : WordTrace (prefixWord ++ tailWord_2047181) baseStart_2047181 baseEnd_2047181 := by
    simpa [prefixWord, tailWord_2047181, baseEnd_2047181] using wordTrace_append hprefix tailTrace_2047181
  have hstable : (prefixWord ++ tailWord_2047181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047181).length < 2 ^ (prefixWord ++ tailWord_2047181).sum := by decide
  have hdescent : baseEnd_2047181 < baseStart_2047181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047330 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2047330 : Nat := 118140960795 + 2047330 * 2 ^ 59
def prefixEnd_2047330 : Nat := 4983230072969 + 3 ^ 40 * 2047330 * 2
def baseEnd_2047330 : Nat := 467228599275368909182003

theorem tailTrace_2047330 : CollatzResearch.WordTrace tailWord_2047330 prefixEnd_2047330 467228599275368909182003 := by
  unfold tailWord_2047330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18668064918220135242890861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49781506448587027314375629 18668064918220135242890861)
  ·
    refine ⟨7000524344332550716084073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18668064918220135242890861 7000524344332550716084073)
    ·
      refine ⟨5250393258249413037063055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7000524344332550716084073 5250393258249413037063055)
      ·
        refine ⟨7875589887374119555594583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250393258249413037063055 7875589887374119555594583)
        ·
          refine ⟨11813384831061179333391875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875589887374119555594583 11813384831061179333391875)
          ·
            refine ⟨17720077246591769000087813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813384831061179333391875 17720077246591769000087813)
            ·
              refine ⟨3322514483735956687516465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17720077246591769000087813 3322514483735956687516465)
              ·
                refine ⟨2491885862801967515637349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3322514483735956687516465 2491885862801967515637349)
                ·
                  refine ⟨467228599275368909182003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2491885862801967515637349 467228599275368909182003)
                  ·
                    rfl

theorem cell21_2047330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2047330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047330 prefixEnd_2047330 := by exact prefixLift 2047330
  have htrace : WordTrace (prefixWord ++ tailWord_2047330) baseStart_2047330 baseEnd_2047330 := by
    simpa [prefixWord, tailWord_2047330, baseEnd_2047330] using wordTrace_append hprefix tailTrace_2047330
  have hstable : (prefixWord ++ tailWord_2047330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047330).length < 2 ^ (prefixWord ++ tailWord_2047330).sum := by decide
  have hdescent : baseEnd_2047330 < baseStart_2047330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047361 : List Nat := [1, 2, 4, 3, 2, 1, 3, 5]
def baseStart_2047361 : Nat := 118140960795 + 2047361 * 2 ^ 59
def prefixEnd_2047361 : Nat := 4983230072969 + 3 ^ 40 * 2047361 * 2
def baseEnd_2047361 : Nat := 155745224632573248055091

theorem tailTrace_2047361 : CollatzResearch.WordTrace tailWord_2047361 prefixEnd_2047361 155745224632573248055091 := by
  unfold tailWord_2047361
  simp only [CollatzResearch.WordTrace]
  refine ⟨74673390335768233265941937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49782260223845488843961291 74673390335768233265941937)
  ·
    refine ⟨56005042751826174949456453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74673390335768233265941937 56005042751826174949456453)
    ·
      refine ⟨10500945515967407803023085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56005042751826174949456453 10500945515967407803023085)
      ·
        refine ⟨3937854568487777926133657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10500945515967407803023085 3937854568487777926133657)
        ·
          refine ⟨2953390926365833444600243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937854568487777926133657 2953390926365833444600243)
          ·
            refine ⟨4430086389548750166900365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953390926365833444600243 4430086389548750166900365)
            ·
              refine ⟨1661282396080781312587637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4430086389548750166900365 1661282396080781312587637)
              ·
                refine ⟨155745224632573248055091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1661282396080781312587637 155745224632573248055091)
                ·
                  rfl

theorem cell21_2047361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 5].length) (baseStart_2047361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047361 prefixEnd_2047361 := by exact prefixLift 2047361
  have htrace : WordTrace (prefixWord ++ tailWord_2047361) baseStart_2047361 baseEnd_2047361 := by
    simpa [prefixWord, tailWord_2047361, baseEnd_2047361] using wordTrace_append hprefix tailTrace_2047361
  have hstable : (prefixWord ++ tailWord_2047361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047361).length < 2 ^ (prefixWord ++ tailWord_2047361).sum := by decide
  have hdescent : baseEnd_2047361 < baseStart_2047361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047372 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_2047372 : Nat := 118140960795 + 2047372 * 2 ^ 59
def prefixEnd_2047372 : Nat := 4983230072969 + 3 ^ 40 * 2047372 * 2
def baseEnd_2047372 : Nat := 467238184247586169481917

theorem tailTrace_2047372 : CollatzResearch.WordTrace tailWord_2047372 prefixEnd_2047372 467238184247586169481917 := by
  unfold tailWord_2047372
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336895769364191072296185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49782527692485588096394913 37336895769364191072296185)
  ·
    refine ⟨28002671827023143304222139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37336895769364191072296185 28002671827023143304222139)
    ·
      refine ⟨42004007740534714956333209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28002671827023143304222139 42004007740534714956333209)
      ·
        refine ⟨31503005805401036217249907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42004007740534714956333209 31503005805401036217249907)
        ·
          refine ⟨47254508708101554325874861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31503005805401036217249907 47254508708101554325874861)
          ·
            refine ⟨17720440765538082872203073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47254508708101554325874861 17720440765538082872203073)
            ·
              refine ⟨13290330574153562154152305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17720440765538082872203073 13290330574153562154152305)
              ·
                refine ⟨9967747930615171615614229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13290330574153562154152305 9967747930615171615614229)
                ·
                  refine ⟨467238184247586169481917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9967747930615171615614229 467238184247586169481917)
                  ·
                    rfl

theorem cell21_2047372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_2047372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047372 prefixEnd_2047372 := by exact prefixLift 2047372
  have htrace : WordTrace (prefixWord ++ tailWord_2047372) baseStart_2047372 baseEnd_2047372 := by
    simpa [prefixWord, tailWord_2047372, baseEnd_2047372] using wordTrace_append hprefix tailTrace_2047372
  have hstable : (prefixWord ++ tailWord_2047372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047372).length < 2 ^ (prefixWord ++ tailWord_2047372).sum := by decide
  have hdescent : baseEnd_2047372 < baseStart_2047372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047389 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2047389 : Nat := 118140960795 + 2047389 * 2 ^ 59
def prefixEnd_2047389 : Nat := 4983230072969 + 3 ^ 40 * 2047389 * 2
def baseEnd_2047389 : Nat := 467242063879197917698549

theorem tailTrace_2047389 : CollatzResearch.WordTrace tailWord_2047389 prefixEnd_2047389 467242063879197917698549 := by
  unfold tailWord_2047389
  simp only [CollatzResearch.WordTrace]
  refine ⟨74674411579666794047961221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49782941053111196031974147 74674411579666794047961221)
  ·
    refine ⟨14001452171187523883992729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74674411579666794047961221 14001452171187523883992729)
    ·
      refine ⟨10501089128390642912994547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14001452171187523883992729 10501089128390642912994547)
      ·
        refine ⟨15751633692585964369491821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501089128390642912994547 15751633692585964369491821)
        ·
          refine ⟨5906862634719736638559433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15751633692585964369491821 5906862634719736638559433)
          ·
            refine ⟨4430146976039802478919575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5906862634719736638559433 4430146976039802478919575)
            ·
              refine ⟨6645220464059703718379363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430146976039802478919575 6645220464059703718379363)
              ·
                refine ⟨9967830696089555577569045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645220464059703718379363 9967830696089555577569045)
                ·
                  refine ⟨467242063879197917698549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9967830696089555577569045 467242063879197917698549)
                  ·
                    rfl

theorem cell21_2047389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2047389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047389 prefixEnd_2047389 := by exact prefixLift 2047389
  have htrace : WordTrace (prefixWord ++ tailWord_2047389) baseStart_2047389 baseEnd_2047389 := by
    simpa [prefixWord, tailWord_2047389, baseEnd_2047389] using wordTrace_append hprefix tailTrace_2047389
  have hstable : (prefixWord ++ tailWord_2047389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047389).length < 2 ^ (prefixWord ++ tailWord_2047389).sum := by decide
  have hdescent : baseEnd_2047389 < baseStart_2047389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
