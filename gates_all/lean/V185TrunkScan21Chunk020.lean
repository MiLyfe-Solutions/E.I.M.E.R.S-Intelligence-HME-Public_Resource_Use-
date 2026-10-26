import V185TrunkScan21Chunk019

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_242350 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_242350 : Nat := 118140960795 + 242350 * 2 ^ 59
def prefixEnd_242350 : Nat := 4983230072969 + 3 ^ 40 * 242350 * 2
def baseEnd_242350 : Nat := 55307571829880905871315

theorem tailTrace_242350 : CollatzResearch.WordTrace tailWord_242350 prefixEnd_242350 55307571829880905871315 := by
  unfold tailWord_242350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104903834001851866234563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5892820448009876619917669 1104903834001851866234563)
  ·
    refine ⟨1657355751002777799351845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104903834001851866234563 1657355751002777799351845)
    ·
      refine ⟨310754203313020837378471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1657355751002777799351845 310754203313020837378471)
      ·
        refine ⟨466131304969531256067707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310754203313020837378471 466131304969531256067707)
        ·
          refine ⟨699196957454296884101561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466131304969531256067707 699196957454296884101561)
          ·
            refine ⟨524397718090722663076171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699196957454296884101561 524397718090722663076171)
            ·
              refine ⟨786596577136083994614257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524397718090722663076171 786596577136083994614257)
              ·
                refine ⟨589947432852062995960693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786596577136083994614257 589947432852062995960693)
                ·
                  refine ⟨55307571829880905871315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589947432852062995960693 55307571829880905871315)
                  ·
                    rfl

theorem cell21_242350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_242350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242350 prefixEnd_242350 := by exact prefixLift 242350
  have htrace : WordTrace (prefixWord ++ tailWord_242350) baseStart_242350 baseEnd_242350 := by
    simpa [prefixWord, tailWord_242350, baseEnd_242350] using wordTrace_append hprefix tailTrace_242350
  have hstable : (prefixWord ++ tailWord_242350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242350).length < 2 ^ (prefixWord ++ tailWord_242350).sum := by decide
  have hdescent : baseEnd_242350 < baseStart_242350 := by decide
  rcases family_descends (prefixWord ++ tailWord_242350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242381 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_242381 : Nat := 118140960795 + 242381 * 2 ^ 59
def prefixEnd_242381 : Nat := 4983230072969 + 3 ^ 40 * 242381 * 2
def baseEnd_242381 : Nat := 55314646452231740854585

theorem tailTrace_242381 : CollatzResearch.WordTrace tailWord_242381 prefixEnd_242381 55314646452231740854585 := by
  unfold tailWord_242381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840361334902507224254997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5893574223268338149503331 8840361334902507224254997)
  ·
    refine ⟨414391937573555026136953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8840361334902507224254997 414391937573555026136953)
    ·
      refine ⟨310793953180166269602715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414391937573555026136953 310793953180166269602715)
      ·
        refine ⟨466190929770249404404073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310793953180166269602715 466190929770249404404073)
        ·
          refine ⟨349643197327687053303055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466190929770249404404073 349643197327687053303055)
          ·
            refine ⟨524464795991530579954583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349643197327687053303055 524464795991530579954583)
            ·
              refine ⟨786697193987295869931875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524464795991530579954583 786697193987295869931875)
              ·
                refine ⟨1180045790980943804897813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786697193987295869931875 1180045790980943804897813)
                ·
                  refine ⟨55314646452231740854585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1180045790980943804897813 55314646452231740854585)
                  ·
                    rfl

theorem cell21_242381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_242381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242381 prefixEnd_242381 := by exact prefixLift 242381
  have htrace : WordTrace (prefixWord ++ tailWord_242381) baseStart_242381 baseEnd_242381 := by
    simpa [prefixWord, tailWord_242381, baseEnd_242381] using wordTrace_append hprefix tailTrace_242381
  have hstable : (prefixWord ++ tailWord_242381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242381).length < 2 ^ (prefixWord ++ tailWord_242381).sum := by decide
  have hdescent : baseEnd_242381 < baseStart_242381 := by decide
  rcases family_descends (prefixWord ++ tailWord_242381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242392 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_242392 : Nat := 118140960795 + 242392 * 2 ^ 59
def prefixEnd_242392 : Nat := 4983230072969 + 3 ^ 40 * 242392 * 2
def baseEnd_242392 : Nat := 55317156802098166171229

theorem tailTrace_242392 : CollatzResearch.WordTrace tailWord_242392 prefixEnd_242392 55317156802098166171229 := by
  unfold tailWord_242392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420381268931328051452715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5893841691908437401936953 4420381268931328051452715)
  ·
    refine ⟨6630571903396992077179073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4420381268931328051452715 6630571903396992077179073)
    ·
      refine ⟨4972928927547744057884305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6630571903396992077179073 4972928927547744057884305)
      ·
        refine ⟨3729696695660808043413229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4972928927547744057884305 3729696695660808043413229)
        ·
          refine ⟨1398636260872803016279961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3729696695660808043413229 1398636260872803016279961)
          ·
            refine ⟨1048977195654602262209971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398636260872803016279961 1048977195654602262209971)
            ·
              refine ⟨1573465793481903393314957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048977195654602262209971 1573465793481903393314957)
              ·
                refine ⟨590049672555713772493109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573465793481903393314957 590049672555713772493109)
                ·
                  refine ⟨55317156802098166171229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 590049672555713772493109 55317156802098166171229)
                  ·
                    rfl

theorem cell21_242392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_242392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242392 prefixEnd_242392 := by exact prefixLift 242392
  have htrace : WordTrace (prefixWord ++ tailWord_242392) baseStart_242392 baseEnd_242392 := by
    simpa [prefixWord, tailWord_242392, baseEnd_242392] using wordTrace_append hprefix tailTrace_242392
  have hstable : (prefixWord ++ tailWord_242392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242392).length < 2 ^ (prefixWord ++ tailWord_242392).sum := by decide
  have hdescent : baseEnd_242392 < baseStart_242392 := by decide
  rcases family_descends (prefixWord ++ tailWord_242392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242499 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_242499 : Nat := 118140960795 + 242499 * 2 ^ 59
def prefixEnd_242499 : Nat := 4983230072969 + 3 ^ 40 * 242499 * 2
def baseEnd_242499 : Nat := 55341575659889757887677

theorem tailTrace_242499 : CollatzResearch.WordTrace tailWord_242499 prefixEnd_242499 55341575659889757887677 := by
  unfold tailWord_242499
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844665148475013377050551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5896443432316675584700367 8844665148475013377050551)
  ·
    refine ⟨13266997722712520065575827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844665148475013377050551 13266997722712520065575827)
    ·
      refine ⟨19900496584068780098363741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13266997722712520065575827 19900496584068780098363741)
      ·
        refine ⟨7462686219025792536886403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19900496584068780098363741 7462686219025792536886403)
        ·
          refine ⟨11194029328538688805329605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7462686219025792536886403 11194029328538688805329605)
          ·
            refine ⟨2098880499101004150999301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11194029328538688805329605 2098880499101004150999301)
            ·
              refine ⟨393540093581438278312369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2098880499101004150999301 393540093581438278312369)
              ·
                refine ⟨295155070186078708734277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393540093581438278312369 295155070186078708734277)
                ·
                  refine ⟨55341575659889757887677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295155070186078708734277 55341575659889757887677)
                  ·
                    rfl

theorem cell21_242499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_242499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242499 prefixEnd_242499 := by exact prefixLift 242499
  have htrace : WordTrace (prefixWord ++ tailWord_242499) baseStart_242499 baseEnd_242499 := by
    simpa [prefixWord, tailWord_242499, baseEnd_242499] using wordTrace_append hprefix tailTrace_242499
  have hstable : (prefixWord ++ tailWord_242499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242499).length < 2 ^ (prefixWord ++ tailWord_242499).sum := by decide
  have hdescent : baseEnd_242499 < baseStart_242499 := by decide
  rcases family_descends (prefixWord ++ tailWord_242499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242589 : List Nat := [1, 4, 2, 1, 2, 1, 3, 7]
def baseStart_242589 : Nat := 118140960795 + 242589 * 2 ^ 59
def prefixEnd_242589 : Nat := 4983230072969 + 3 ^ 40 * 242589 * 2
def baseEnd_242589 : Nat := 18454038295356533795831

theorem tailTrace_242589 : CollatzResearch.WordTrace tailWord_242589 prefixEnd_242589 18454038295356533795831 := by
  unfold tailWord_242589
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847947718148958747826821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5898631812099305831884547 8847947718148958747826821)
  ·
    refine ⟨1658990197152929765217529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8847947718148958747826821 1658990197152929765217529)
    ·
      refine ⟨1244242647864697323913147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1658990197152929765217529 1244242647864697323913147)
      ·
        refine ⟨1866363971797045985869721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244242647864697323913147 1866363971797045985869721)
        ·
          refine ⟨1399772978847784489402291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866363971797045985869721 1399772978847784489402291)
          ·
            refine ⟨2099659468271676734103437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399772978847784489402291 2099659468271676734103437)
            ·
              refine ⟨787372300601878775288789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099659468271676734103437 787372300601878775288789)
              ·
                refine ⟨18454038295356533795831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 787372300601878775288789 18454038295356533795831)
                ·
                  rfl

theorem cell21_242589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_242589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242589 prefixEnd_242589 := by exact prefixLift 242589
  have htrace : WordTrace (prefixWord ++ tailWord_242589) baseStart_242589 baseEnd_242589 := by
    simpa [prefixWord, tailWord_242589, baseEnd_242589] using wordTrace_append hprefix tailTrace_242589
  have hstable : (prefixWord ++ tailWord_242589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242589).length < 2 ^ (prefixWord ++ tailWord_242589).sum := by decide
  have hdescent : baseEnd_242589 < baseStart_242589 := by decide
  rcases family_descends (prefixWord ++ tailWord_242589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242612 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_242612 : Nat := 118140960795 + 242612 * 2 ^ 59
def prefixEnd_242612 : Nat := 4983230072969 + 3 ^ 40 * 242612 * 2
def baseEnd_242612 : Nat := 55367363799426672504113

theorem tailTrace_242612 : CollatzResearch.WordTrace tailWord_242612 prefixEnd_242612 55367363799426672504113 := by
  unfold tailWord_242612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424393298532816837957045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5899191064710422450609393 4424393298532816837957045)
  ·
    refine ⟨414786871737451578558473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4424393298532816837957045 414786871737451578558473)
    ·
      refine ⟨311090153803088683918855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414786871737451578558473 311090153803088683918855)
      ·
        refine ⟨466635230704633025878283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311090153803088683918855 466635230704633025878283)
        ·
          refine ⟨699952846056949538817425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466635230704633025878283 699952846056949538817425)
          ·
            refine ⟨524964634542712154113069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699952846056949538817425 524964634542712154113069)
            ·
              refine ⟨196861737953517057792401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524964634542712154113069 196861737953517057792401)
              ·
                refine ⟨147646303465137793344301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196861737953517057792401 147646303465137793344301)
                ·
                  refine ⟨55367363799426672504113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147646303465137793344301 55367363799426672504113)
                  ·
                    rfl

theorem cell21_242612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_242612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242612 prefixEnd_242612 := by exact prefixLift 242612
  have htrace : WordTrace (prefixWord ++ tailWord_242612) baseStart_242612 baseEnd_242612 := by
    simpa [prefixWord, tailWord_242612, baseEnd_242612] using wordTrace_append hprefix tailTrace_242612
  have hstable : (prefixWord ++ tailWord_242612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242612).length < 2 ^ (prefixWord ++ tailWord_242612).sum := by decide
  have hdescent : baseEnd_242612 < baseStart_242612 := by decide
  rcases family_descends (prefixWord ++ tailWord_242612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242696 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_242696 : Nat := 118140960795 + 242696 * 2 ^ 59
def prefixEnd_242696 : Nat := 4983230072969 + 3 ^ 40 * 242696 * 2
def baseEnd_242696 : Nat := 55386533743861193103941

theorem tailTrace_242696 : CollatzResearch.WordTrace tailWord_242696 prefixEnd_242696 55386533743861193103941 := by
  unfold tailWord_242696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425925164380658010985971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5901233552507544014647961 4425925164380658010985971)
  ·
    refine ⟨6638887746570987016478957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425925164380658010985971 6638887746570987016478957)
    ·
      refine ⟨2489582904964120131179609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6638887746570987016478957 2489582904964120131179609)
      ·
        refine ⟨1867187178723090098384707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489582904964120131179609 1867187178723090098384707)
        ·
          refine ⟨2800780768084635147577061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867187178723090098384707 2800780768084635147577061)
          ·
            refine ⟨525146394015869090170699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2800780768084635147577061 525146394015869090170699)
            ·
              refine ⟨787719591023803635256049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525146394015869090170699 787719591023803635256049)
              ·
                refine ⟨590789693267852726442037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787719591023803635256049 590789693267852726442037)
                ·
                  refine ⟨55386533743861193103941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 590789693267852726442037 55386533743861193103941)
                  ·
                    rfl

theorem cell21_242696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_242696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242696 prefixEnd_242696 := by exact prefixLift 242696
  have htrace : WordTrace (prefixWord ++ tailWord_242696) baseStart_242696 baseEnd_242696 := by
    simpa [prefixWord, tailWord_242696, baseEnd_242696] using wordTrace_append hprefix tailTrace_242696
  have hstable : (prefixWord ++ tailWord_242696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242696).length < 2 ^ (prefixWord ++ tailWord_242696).sum := by decide
  have hdescent : baseEnd_242696 < baseStart_242696 := by decide
  rcases family_descends (prefixWord ++ tailWord_242696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242744 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_242744 : Nat := 118140960795 + 242744 * 2 ^ 59
def prefixEnd_242744 : Nat := 4983230072969 + 3 ^ 40 * 242744 * 2
def baseEnd_242744 : Nat := 55397487997823776303843

theorem tailTrace_242744 : CollatzResearch.WordTrace tailWord_242744 prefixEnd_242744 55397487997823776303843 := by
  unfold tailWord_242744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426800516293710109859643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5902400688391613479812857 4426800516293710109859643)
  ·
    refine ⟨6640200774440565164789465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4426800516293710109859643 6640200774440565164789465)
    ·
      refine ⟨4980150580830423873592099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6640200774440565164789465 4980150580830423873592099)
      ·
        refine ⟨7470225871245635810388149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980150580830423873592099 7470225871245635810388149)
        ·
          refine ⟨700333675429278357223889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7470225871245635810388149 700333675429278357223889)
          ·
            refine ⟨525250256571958767917917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700333675429278357223889 525250256571958767917917)
            ·
              refine ⟨196968846214484537969219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525250256571958767917917 196968846214484537969219)
              ·
                refine ⟨295453269321726806953829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196968846214484537969219 295453269321726806953829)
                ·
                  refine ⟨55397487997823776303843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295453269321726806953829 55397487997823776303843)
                  ·
                    rfl

theorem cell21_242744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_242744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242744 prefixEnd_242744 := by exact prefixLift 242744
  have htrace : WordTrace (prefixWord ++ tailWord_242744) baseStart_242744 baseEnd_242744 := by
    simpa [prefixWord, tailWord_242744, baseEnd_242744] using wordTrace_append hprefix tailTrace_242744
  have hstable : (prefixWord ++ tailWord_242744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242744).length < 2 ^ (prefixWord ++ tailWord_242744).sum := by decide
  have hdescent : baseEnd_242744 < baseStart_242744 := by decide
  rcases family_descends (prefixWord ++ tailWord_242744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242755 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_242755 : Nat := 118140960795 + 242755 * 2 ^ 59
def prefixEnd_242755 : Nat := 4983230072969 + 3 ^ 40 * 242755 * 2
def baseEnd_242755 : Nat := 55399998347690201620487

theorem tailTrace_242755 : CollatzResearch.WordTrace tailWord_242755 prefixEnd_242755 55399998347690201620487 := by
  unfold tailWord_242755
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854002235547569098369719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5902668157031712732246479 8854002235547569098369719)
  ·
    refine ⟨13281003353321353647554579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8854002235547569098369719 13281003353321353647554579)
    ·
      refine ⟨19921505029982030471331869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13281003353321353647554579 19921505029982030471331869)
      ·
        refine ⟨7470564386243261426749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19921505029982030471331869 7470564386243261426749451)
        ·
          refine ⟨11205846579364892140124177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470564386243261426749451 11205846579364892140124177)
          ·
            refine ⟨8404384934523669105093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11205846579364892140124177 8404384934523669105093133)
            ·
              refine ⟨3151644350446375914409925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8404384934523669105093133 3151644350446375914409925)
              ·
                refine ⟨590933315708695483951861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3151644350446375914409925 590933315708695483951861)
                ·
                  refine ⟨55399998347690201620487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 590933315708695483951861 55399998347690201620487)
                  ·
                    rfl

theorem cell21_242755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_242755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242755 prefixEnd_242755 := by exact prefixLift 242755
  have htrace : WordTrace (prefixWord ++ tailWord_242755) baseStart_242755 baseEnd_242755 := by
    simpa [prefixWord, tailWord_242755, baseEnd_242755] using wordTrace_append hprefix tailTrace_242755
  have hstable : (prefixWord ++ tailWord_242755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242755).length < 2 ^ (prefixWord ++ tailWord_242755).sum := by decide
  have hdescent : baseEnd_242755 < baseStart_242755 := by decide
  rcases family_descends (prefixWord ++ tailWord_242755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242817 : List Nat := [1, 2, 4, 2, 2, 1, 2, 7]
def baseStart_242817 : Nat := 118140960795 + 242817 * 2 ^ 59
def prefixEnd_242817 : Nat := 4983230072969 + 3 ^ 40 * 242817 * 2
def baseEnd_242817 : Nat := 18471382530797290529009

theorem tailTrace_242817 : CollatzResearch.WordTrace tailWord_242817 prefixEnd_242817 18471382530797290529009 := by
  unfold tailWord_242817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856263561322953687126705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5904175707548635791417803 8856263561322953687126705)
  ·
    refine ⟨6642197670992215265345029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8856263561322953687126705 6642197670992215265345029)
    ·
      refine ⟨1245412063311040362252193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6642197670992215265345029 1245412063311040362252193)
      ·
        refine ⟨934059047483280271689145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245412063311040362252193 934059047483280271689145)
        ·
          refine ⟨700544285612460203766859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934059047483280271689145 700544285612460203766859)
          ·
            refine ⟨1050816428418690305650289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700544285612460203766859 1050816428418690305650289)
            ·
              refine ⟨788112321314017729237717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050816428418690305650289 788112321314017729237717)
              ·
                refine ⟨18471382530797290529009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 788112321314017729237717 18471382530797290529009)
                ·
                  rfl

theorem cell21_242817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_242817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242817 prefixEnd_242817 := by exact prefixLift 242817
  have htrace : WordTrace (prefixWord ++ tailWord_242817) baseStart_242817 baseEnd_242817 := by
    simpa [prefixWord, tailWord_242817, baseEnd_242817] using wordTrace_append hprefix tailTrace_242817
  have hstable : (prefixWord ++ tailWord_242817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242817).length < 2 ^ (prefixWord ++ tailWord_242817).sum := by decide
  have hdescent : baseEnd_242817 < baseStart_242817 := by decide
  rcases family_descends (prefixWord ++ tailWord_242817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242921 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_242921 : Nat := 118140960795 + 242921 * 2 ^ 59
def prefixEnd_242921 : Nat := 4983230072969 + 3 ^ 40 * 242921 * 2
def baseEnd_242921 : Nat := 55437881809310801853481

theorem tailTrace_242921 : CollatzResearch.WordTrace tailWord_242921 prefixEnd_242921 55437881809310801853481 := by
  unfold tailWord_242921
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860056752946179448912617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5906704501964119632608411 8860056752946179448912617)
  ·
    refine ⟨6645042564709634586684463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8860056752946179448912617 6645042564709634586684463)
    ·
      refine ⟨9967563847064451880026695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645042564709634586684463 9967563847064451880026695)
      ·
        refine ⟨14951345770596677820040043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967563847064451880026695 14951345770596677820040043)
        ·
          refine ⟨22427018655895016730060065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14951345770596677820040043 22427018655895016730060065)
          ·
            refine ⟨16820263991921262547545049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22427018655895016730060065 16820263991921262547545049)
            ·
              refine ⟨12615197993940946910658787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16820263991921262547545049 12615197993940946910658787)
              ·
                refine ⟨18922796990911420365988181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12615197993940946910658787 18922796990911420365988181)
                ·
                  refine ⟨55437881809310801853481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18922796990911420365988181 55437881809310801853481)
                  ·
                    rfl

theorem cell21_242921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_242921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242921 prefixEnd_242921 := by exact prefixLift 242921
  have htrace : WordTrace (prefixWord ++ tailWord_242921) baseStart_242921 baseEnd_242921 := by
    simpa [prefixWord, tailWord_242921, baseEnd_242921] using wordTrace_append hprefix tailTrace_242921
  have hstable : (prefixWord ++ tailWord_242921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242921).length < 2 ^ (prefixWord ++ tailWord_242921).sum := by decide
  have hdescent : baseEnd_242921 < baseStart_242921 := by decide
  rcases family_descends (prefixWord ++ tailWord_242921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242927 : List Nat := [1, 1, 2, 1, 8, 1, 2, 5]
def baseStart_242927 : Nat := 118140960795 + 242927 * 2 ^ 59
def prefixEnd_242927 : Nat := 4983230072969 + 3 ^ 40 * 242927 * 2
def baseEnd_242927 : Nat := 18479750363685374917823

theorem tailTrace_242927 : CollatzResearch.WordTrace tailWord_242927 prefixEnd_242927 18479750363685374917823 := by
  unfold tailWord_242927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860275590924442473631035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5906850393949628315754023 8860275590924442473631035)
  ·
    refine ⟨13290413386386663710446553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8860275590924442473631035 13290413386386663710446553)
    ·
      refine ⟨9967810039789997782834915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13290413386386663710446553 9967810039789997782834915)
      ·
        refine ⟨14951715059684996674252373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967810039789997782834915 14951715059684996674252373)
        ·
          refine ⟨175215410855683554776395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 14951715059684996674252373 175215410855683554776395)
          ·
            refine ⟨262823116283525332164593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175215410855683554776395 262823116283525332164593)
            ·
              refine ⟨197117337212643999123445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262823116283525332164593 197117337212643999123445)
              ·
                refine ⟨18479750363685374917823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197117337212643999123445 18479750363685374917823)
                ·
                  rfl

theorem cell21_242927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 5].length) (baseStart_242927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242927 prefixEnd_242927 := by exact prefixLift 242927
  have htrace : WordTrace (prefixWord ++ tailWord_242927) baseStart_242927 baseEnd_242927 := by
    simpa [prefixWord, tailWord_242927, baseEnd_242927] using wordTrace_append hprefix tailTrace_242927
  have hstable : (prefixWord ++ tailWord_242927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242927).length < 2 ^ (prefixWord ++ tailWord_242927).sum := by decide
  have hdescent : baseEnd_242927 < baseStart_242927 := by decide
  rcases family_descends (prefixWord ++ tailWord_242927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242958 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_242958 : Nat := 118140960795 + 242958 * 2 ^ 59
def prefixEnd_242958 : Nat := 4983230072969 + 3 ^ 40 * 242958 * 2
def baseEnd_242958 : Nat := 55446325713406959736739

theorem tailTrace_242958 : CollatzResearch.WordTrace tailWord_242958 prefixEnd_242958 55446325713406959736739 := by
  unfold tailWord_242958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107675781726516846001191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5907604169208089845339685 1107675781726516846001191)
  ·
    refine ⟨1661513672589775269001787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107675781726516846001191 1661513672589775269001787)
    ·
      refine ⟨2492270508884662903502681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661513672589775269001787 2492270508884662903502681)
      ·
        refine ⟨1869202881663497177627011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2492270508884662903502681 1869202881663497177627011)
        ·
          refine ⟨2803804322495245766440517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869202881663497177627011 2803804322495245766440517)
          ·
            refine ⟨525713310467858581207597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2803804322495245766440517 525713310467858581207597)
            ·
              refine ⟨197142491425446967952849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525713310467858581207597 197142491425446967952849)
              ·
                refine ⟨147856868569085225964637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197142491425446967952849 147856868569085225964637)
                ·
                  refine ⟨55446325713406959736739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147856868569085225964637 55446325713406959736739)
                  ·
                    rfl

theorem cell21_242958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_242958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242958 prefixEnd_242958 := by exact prefixLift 242958
  have htrace : WordTrace (prefixWord ++ tailWord_242958) baseStart_242958 baseEnd_242958 := by
    simpa [prefixWord, tailWord_242958, baseEnd_242958] using wordTrace_append hprefix tailTrace_242958
  have hstable : (prefixWord ++ tailWord_242958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242958).length < 2 ^ (prefixWord ++ tailWord_242958).sum := by decide
  have hdescent : baseEnd_242958 < baseStart_242958 := by decide
  rcases family_descends (prefixWord ++ tailWord_242958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243000 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_243000 : Nat := 118140960795 + 243000 * 2 ^ 59
def prefixEnd_243000 : Nat := 4983230072969 + 3 ^ 40 * 243000 * 2
def baseEnd_243000 : Nat := 55455910685624220036653

theorem tailTrace_243000 : CollatzResearch.WordTrace tailWord_243000 prefixEnd_243000 55455910685624220036653 := by
  unfold tailWord_243000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431469059829987970519227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5908625413106650627358969 4431469059829987970519227)
  ·
    refine ⟨6647203589744981955778841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4431469059829987970519227 6647203589744981955778841)
    ·
      refine ⟨4985402692308736466834131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6647203589744981955778841 4985402692308736466834131)
      ·
        refine ⟨7478104038463104700251197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985402692308736466834131 7478104038463104700251197)
        ·
          refine ⟨2804289014423664262594199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7478104038463104700251197 2804289014423664262594199)
          ·
            refine ⟨4206433521635496393891299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804289014423664262594199 4206433521635496393891299)
            ·
              refine ⟨6309650282453244590836949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206433521635496393891299 6309650282453244590836949)
              ·
                refine ⟨147882428494997920097741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6309650282453244590836949 147882428494997920097741)
                ·
                  refine ⟨55455910685624220036653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147882428494997920097741 55455910685624220036653)
                  ·
                    rfl

theorem cell21_243000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_243000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243000 prefixEnd_243000 := by exact prefixLift 243000
  have htrace : WordTrace (prefixWord ++ tailWord_243000) baseStart_243000 baseEnd_243000 := by
    simpa [prefixWord, tailWord_243000, baseEnd_243000] using wordTrace_append hprefix tailTrace_243000
  have hstable : (prefixWord ++ tailWord_243000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243000).length < 2 ^ (prefixWord ++ tailWord_243000).sum := by decide
  have hdescent : baseEnd_243000 < baseStart_243000 := by decide
  rcases family_descends (prefixWord ++ tailWord_243000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243017 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 3]
def baseStart_243017 : Nat := 118140960795 + 243017 * 2 ^ 59
def prefixEnd_243017 : Nat := 4983230072969 + 3 ^ 40 * 243017 * 2
def baseEnd_243017 : Nat := 55459790317235968253285

theorem tailTrace_243017 : CollatzResearch.WordTrace tailWord_243017 prefixEnd_243017 55459790317235968253285 := by
  unfold tailWord_243017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863558160598387844407305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5909038773732258562938203 8863558160598387844407305)
  ·
    refine ⟨6647668620448790883305479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8863558160598387844407305 6647668620448790883305479)
    ·
      refine ⟨9971502930673186324958219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6647668620448790883305479 9971502930673186324958219)
      ·
        refine ⟨14957254396009779487437329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9971502930673186324958219 14957254396009779487437329)
        ·
          refine ⟨11217940797007334615577997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14957254396009779487437329 11217940797007334615577997)
          ·
            refine ⟨4206727798877750480841749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11217940797007334615577997 4206727798877750480841749)
            ·
              refine ⟨197190365572394553789457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4206727798877750480841749 197190365572394553789457)
              ·
                refine ⟨147892774179295915342093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197190365572394553789457 147892774179295915342093)
                ·
                  refine ⟨55459790317235968253285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147892774179295915342093 55459790317235968253285)
                  ·
                    rfl

theorem cell21_243017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_243017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243017 prefixEnd_243017 := by exact prefixLift 243017
  have htrace : WordTrace (prefixWord ++ tailWord_243017) baseStart_243017 baseEnd_243017 := by
    simpa [prefixWord, tailWord_243017, baseEnd_243017] using wordTrace_append hprefix tailTrace_243017
  have hstable : (prefixWord ++ tailWord_243017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243017).length < 2 ^ (prefixWord ++ tailWord_243017).sum := by decide
  have hdescent : baseEnd_243017 < baseStart_243017 := by decide
  rcases family_descends (prefixWord ++ tailWord_243017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243045 : List Nat := [1, 3, 1, 3, 1, 2, 5, 5]
def baseStart_243045 : Nat := 118140960795 + 243045 * 2 ^ 59
def prefixEnd_243045 : Nat := 4983230072969 + 3 ^ 40 * 243045 * 2
def baseEnd_243045 : Nat := 18488726766238047262187

theorem tailTrace_243045 : CollatzResearch.WordTrace tailWord_243045 prefixEnd_243045 18488726766238047262187 := by
  unfold tailWord_243045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864579404496948626426589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5909719602997965750951059 8864579404496948626426589)
  ·
    refine ⟨3324217276686355734909971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8864579404496948626426589 3324217276686355734909971)
    ·
      refine ⟨4986325915029533602364957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324217276686355734909971 4986325915029533602364957)
      ·
        refine ⟨1869872218136075100886859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4986325915029533602364957 1869872218136075100886859)
        ·
          refine ⟨2804808327204112651330289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869872218136075100886859 2804808327204112651330289)
          ·
            refine ⟨2103606245403084488497717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2804808327204112651330289 2103606245403084488497717)
            ·
              refine ⟨197213085506539170796661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2103606245403084488497717 197213085506539170796661)
              ·
                refine ⟨18488726766238047262187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197213085506539170796661 18488726766238047262187)
                ·
                  rfl

theorem cell21_243045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 5].length) (baseStart_243045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243045 prefixEnd_243045 := by exact prefixLift 243045
  have htrace : WordTrace (prefixWord ++ tailWord_243045) baseStart_243045 baseEnd_243045 := by
    simpa [prefixWord, tailWord_243045, baseEnd_243045] using wordTrace_append hprefix tailTrace_243045
  have hstable : (prefixWord ++ tailWord_243045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243045).length < 2 ^ (prefixWord ++ tailWord_243045).sum := by decide
  have hdescent : baseEnd_243045 < baseStart_243045 := by decide
  rcases family_descends (prefixWord ++ tailWord_243045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243076 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_243076 : Nat := 118140960795 + 243076 * 2 ^ 59
def prefixEnd_243076 : Nat := 4983230072969 + 3 ^ 40 * 243076 * 2
def baseEnd_243076 : Nat := 55473254921064976769831

theorem tailTrace_243076 : CollatzResearch.WordTrace tailWord_243076 prefixEnd_243076 55473254921064976769831 := by
  unfold tailWord_243076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432855033692320460402541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5910473378256427280536721 4432855033692320460402541)
  ·
    refine ⟨1662320637634620172650953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4432855033692320460402541 1662320637634620172650953)
    ·
      refine ⟨1246740478225965129488215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1662320637634620172650953 1246740478225965129488215)
      ·
        refine ⟨1870110717338947694232323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246740478225965129488215 1870110717338947694232323)
        ·
          refine ⟨2805166076008421541348485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870110717338947694232323 2805166076008421541348485)
          ·
            refine ⟨525968639251579039002841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2805166076008421541348485 525968639251579039002841)
            ·
              refine ⟨394476479438684279252131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525968639251579039002841 394476479438684279252131)
              ·
                refine ⟨591714719158026418878197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394476479438684279252131 591714719158026418878197)
                ·
                  refine ⟨55473254921064976769831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591714719158026418878197 55473254921064976769831)
                  ·
                    rfl

theorem cell21_243076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_243076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243076 prefixEnd_243076 := by exact prefixLift 243076
  have htrace : WordTrace (prefixWord ++ tailWord_243076) baseStart_243076 baseEnd_243076 := by
    simpa [prefixWord, tailWord_243076, baseEnd_243076] using wordTrace_append hprefix tailTrace_243076
  have hstable : (prefixWord ++ tailWord_243076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243076).length < 2 ^ (prefixWord ++ tailWord_243076).sum := by decide
  have hdescent : baseEnd_243076 < baseStart_243076 := by decide
  rcases family_descends (prefixWord ++ tailWord_243076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243104 : List Nat := [2, 1, 1, 4, 1, 2, 3, 7]
def baseStart_243104 : Nat := 118140960795 + 243104 * 2 ^ 59
def prefixEnd_243104 : Nat := 4983230072969 + 3 ^ 40 * 243104 * 2
def baseEnd_243104 : Nat := 18493214967514383434369

theorem tailTrace_243104 : CollatzResearch.WordTrace tailWord_243104 prefixEnd_243104 18493214967514383434369 := by
  unfold tailWord_243104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433365655641600851412183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5911154207522134468549577 4433365655641600851412183)
  ·
    refine ⟨6650048483462401277118275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433365655641600851412183 6650048483462401277118275)
    ·
      refine ⟨9975072725193601915677413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650048483462401277118275 9975072725193601915677413)
      ·
        refine ⟨1870326135973800359189515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9975072725193601915677413 1870326135973800359189515)
        ·
          refine ⟨2805489203960700538784273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870326135973800359189515 2805489203960700538784273)
          ·
            refine ⟨2104116902970525404088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2805489203960700538784273 2104116902970525404088205)
            ·
              refine ⟨789043838613947026533077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104116902970525404088205 789043838613947026533077)
              ·
                refine ⟨18493214967514383434369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 789043838613947026533077 18493214967514383434369)
                ·
                  rfl

theorem cell21_243104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_243104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243104 prefixEnd_243104 := by exact prefixLift 243104
  have htrace : WordTrace (prefixWord ++ tailWord_243104) baseStart_243104 baseEnd_243104 := by
    simpa [prefixWord, tailWord_243104, baseEnd_243104] using wordTrace_append hprefix tailTrace_243104
  have hstable : (prefixWord ++ tailWord_243104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243104).length < 2 ^ (prefixWord ++ tailWord_243104).sum := by decide
  have hdescent : baseEnd_243104 < baseStart_243104 := by decide
  rcases family_descends (prefixWord ++ tailWord_243104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243186 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_243186 : Nat := 118140960795 + 243186 * 2 ^ 59
def prefixEnd_243186 : Nat := 4983230072969 + 3 ^ 40 * 243186 * 2
def baseEnd_243186 : Nat := 55498358419729229936273

theorem tailTrace_243186 : CollatzResearch.WordTrace tailWord_243186 prefixEnd_243186 55498358419729229936273 := by
  unfold tailWord_243186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217430524246532426827353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5913148064657419804872941 2217430524246532426827353)
  ·
    refine ⟨1663072893184899320120515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2217430524246532426827353 1663072893184899320120515)
    ·
      refine ⟨2494609339777348980180773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663072893184899320120515 2494609339777348980180773)
      ·
        refine ⟨467739251208252933783895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2494609339777348980180773 467739251208252933783895)
        ·
          refine ⟨701608876812379400675843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467739251208252933783895 701608876812379400675843)
          ·
            refine ⟨1052413315218569101013765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701608876812379400675843 1052413315218569101013765)
            ·
              refine ⟨197327496603481706440081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1052413315218569101013765 197327496603481706440081)
              ·
                refine ⟨147995622452611279830061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197327496603481706440081 147995622452611279830061)
                ·
                  refine ⟨55498358419729229936273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147995622452611279830061 55498358419729229936273)
                  ·
                    rfl

theorem cell21_243186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_243186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243186 prefixEnd_243186 := by exact prefixLift 243186
  have htrace : WordTrace (prefixWord ++ tailWord_243186) baseStart_243186 baseEnd_243186 := by
    simpa [prefixWord, tailWord_243186, baseEnd_243186] using wordTrace_append hprefix tailTrace_243186
  have hstable : (prefixWord ++ tailWord_243186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243186).length < 2 ^ (prefixWord ++ tailWord_243186).sum := by decide
  have hdescent : baseEnd_243186 < baseStart_243186 := by decide
  rcases family_descends (prefixWord ++ tailWord_243186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243197 : List Nat := [1, 4, 1, 1, 1, 6, 1, 6]
def baseStart_243197 : Nat := 118140960795 + 243197 * 2 ^ 59
def prefixEnd_243197 : Nat := 4983230072969 + 3 ^ 40 * 243197 * 2
def baseEnd_243197 : Nat := 18500289589865218417639

theorem tailTrace_243197 : CollatzResearch.WordTrace tailWord_243197 prefixEnd_243197 18500289589865218417639 := by
  unfold tailWord_243197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8870123299946278585959845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5913415533297519057306563 8870123299946278585959845)
  ·
    refine ⟨1663148118739927234867471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8870123299946278585959845 1663148118739927234867471)
    ·
      refine ⟨2494722178109890852301207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663148118739927234867471 2494722178109890852301207)
      ·
        refine ⟨3742083267164836278451811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494722178109890852301207 3742083267164836278451811)
        ·
          refine ⟨5613124900747254417677717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742083267164836278451811 5613124900747254417677717)
          ·
            refine ⟨263115229722527550828643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5613124900747254417677717 263115229722527550828643)
            ·
              refine ⟨394672844583791326242965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263115229722527550828643 394672844583791326242965)
              ·
                refine ⟨18500289589865218417639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 394672844583791326242965 18500289589865218417639)
                ·
                  rfl

theorem cell21_243197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 6].length) (baseStart_243197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243197 prefixEnd_243197 := by exact prefixLift 243197
  have htrace : WordTrace (prefixWord ++ tailWord_243197) baseStart_243197 baseEnd_243197 := by
    simpa [prefixWord, tailWord_243197, baseEnd_243197] using wordTrace_append hprefix tailTrace_243197
  have hstable : (prefixWord ++ tailWord_243197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243197).length < 2 ^ (prefixWord ++ tailWord_243197).sum := by decide
  have hdescent : baseEnd_243197 < baseStart_243197 := by decide
  rcases family_descends (prefixWord ++ tailWord_243197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243214 : List Nat := [4, 1, 1, 2, 4, 1, 3, 5]
def baseStart_243214 : Nat := 118140960795 + 243214 * 2 ^ 59
def prefixEnd_243214 : Nat := 4983230072969 + 3 ^ 40 * 243214 * 2
def baseEnd_243214 : Nat := 18501582800402467823183

theorem tailTrace_243214 : CollatzResearch.WordTrace tailWord_243214 prefixEnd_243214 18501582800402467823183 := by
  unfold tailWord_243214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108842917610586311166087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5913828893923126992885797 1108842917610586311166087)
  ·
    refine ⟨1663264376415879466749131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1108842917610586311166087 1663264376415879466749131)
    ·
      refine ⟨2494896564623819200123697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1663264376415879466749131 2494896564623819200123697)
      ·
        refine ⟨1871172423467864400092773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2494896564623819200123697 1871172423467864400092773)
        ·
          refine ⟨350844829400224575017395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1871172423467864400092773 350844829400224575017395)
          ·
            refine ⟨526267244100336862526093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350844829400224575017395 526267244100336862526093)
            ·
              refine ⟨197350216537626323447285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526267244100336862526093 197350216537626323447285)
              ·
                refine ⟨18501582800402467823183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197350216537626323447285 18501582800402467823183)
                ·
                  rfl

theorem cell21_243214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_243214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243214 prefixEnd_243214 := by exact prefixLift 243214
  have htrace : WordTrace (prefixWord ++ tailWord_243214) baseStart_243214 baseEnd_243214 := by
    simpa [prefixWord, tailWord_243214, baseEnd_243214] using wordTrace_append hprefix tailTrace_243214
  have hstable : (prefixWord ++ tailWord_243214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243214).length < 2 ^ (prefixWord ++ tailWord_243214).sum := by decide
  have hdescent : baseEnd_243214 < baseStart_243214 := by decide
  rcases family_descends (prefixWord ++ tailWord_243214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243242 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_243242 : Nat := 118140960795 + 243242 * 2 ^ 59
def prefixEnd_243242 : Nat := 4983230072969 + 3 ^ 40 * 243242 * 2
def baseEnd_243242 : Nat := 55511138382685577002825

theorem tailTrace_243242 : CollatzResearch.WordTrace tailWord_243242 prefixEnd_243242 55511138382685577002825 := by
  unfold tailWord_243242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217941146195812817836995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5914509723188834180898653 2217941146195812817836995)
  ·
    refine ⟨3326911719293719226755493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217941146195812817836995 3326911719293719226755493)
    ·
      refine ⟨623795947367572355016655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3326911719293719226755493 623795947367572355016655)
      ·
        refine ⟨935693921051358532524983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623795947367572355016655 935693921051358532524983)
        ·
          refine ⟨1403540881577037798787475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935693921051358532524983 1403540881577037798787475)
          ·
            refine ⟨2105311322365556698181213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403540881577037798787475 2105311322365556698181213)
            ·
              refine ⟨789491745887083761817955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2105311322365556698181213 789491745887083761817955)
              ·
                refine ⟨1184237618830625642726933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789491745887083761817955 1184237618830625642726933)
                ·
                  refine ⟨55511138382685577002825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1184237618830625642726933 55511138382685577002825)
                  ·
                    rfl

theorem cell21_243242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_243242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243242 prefixEnd_243242 := by exact prefixLift 243242
  have htrace : WordTrace (prefixWord ++ tailWord_243242) baseStart_243242 baseEnd_243242 := by
    simpa [prefixWord, tailWord_243242, baseEnd_243242] using wordTrace_append hprefix tailTrace_243242
  have hstable : (prefixWord ++ tailWord_243242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243242).length < 2 ^ (prefixWord ++ tailWord_243242).sum := by decide
  have hdescent : baseEnd_243242 < baseStart_243242 := by decide
  rcases family_descends (prefixWord ++ tailWord_243242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243304 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_243304 : Nat := 118140960795 + 243304 * 2 ^ 59
def prefixEnd_243304 : Nat := 4983230072969 + 3 ^ 40 * 243304 * 2
def baseEnd_243304 : Nat := 55525287627387246969365

theorem tailTrace_243304 : CollatzResearch.WordTrace tailWord_243304 prefixEnd_243304 55525287627387246969365 := by
  unfold tailWord_243304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437012955279317930052483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5916017273705757240069977 4437012955279317930052483)
  ·
    refine ⟨6655519432918976895078725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437012955279317930052483 6655519432918976895078725)
    ·
      refine ⟨1247909893672308167827261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6655519432918976895078725 1247909893672308167827261)
      ·
        refine ⟨467966210127115562935223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1247909893672308167827261 467966210127115562935223)
        ·
          refine ⟨701949315190673344402835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467966210127115562935223 701949315190673344402835)
          ·
            refine ⟨1052923972786010016604253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701949315190673344402835 1052923972786010016604253)
            ·
              refine ⟨394846489794753756226595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052923972786010016604253 394846489794753756226595)
              ·
                refine ⟨592269734692130634339893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394846489794753756226595 592269734692130634339893)
                ·
                  refine ⟨55525287627387246969365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592269734692130634339893 55525287627387246969365)
                  ·
                    rfl

theorem cell21_243304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_243304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243304 prefixEnd_243304 := by exact prefixLift 243304
  have htrace : WordTrace (prefixWord ++ tailWord_243304) baseStart_243304 baseEnd_243304 := by
    simpa [prefixWord, tailWord_243304, baseEnd_243304] using wordTrace_append hprefix tailTrace_243304
  have hstable : (prefixWord ++ tailWord_243304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243304).length < 2 ^ (prefixWord ++ tailWord_243304).sum := by decide
  have hdescent : baseEnd_243304 < baseStart_243304 := by decide
  rcases family_descends (prefixWord ++ tailWord_243304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243414 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_243414 : Nat := 118140960795 + 243414 * 2 ^ 59
def prefixEnd_243414 : Nat := 4983230072969 + 3 ^ 40 * 243414 * 2
def baseEnd_243414 : Nat := 55550391126051500135807

theorem tailTrace_243414 : CollatzResearch.WordTrace tailWord_243414 prefixEnd_243414 55550391126051500135807 := by
  unfold tailWord_243414
  simp only [CollatzResearch.WordTrace]
  refine ⟨554877371260007790413081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5918691960106749764406197 554877371260007790413081)
  ·
    refine ⟨416158028445005842809811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 554877371260007790413081 416158028445005842809811)
    ·
      refine ⟨624237042667508764214717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416158028445005842809811 624237042667508764214717)
      ·
        refine ⟨234088891000315786580519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624237042667508764214717 234088891000315786580519)
        ·
          refine ⟨351133336500473679870779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234088891000315786580519 351133336500473679870779)
          ·
            refine ⟨526700004750710519806169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351133336500473679870779 526700004750710519806169)
            ·
              refine ⟨395025003563032889854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526700004750710519806169 395025003563032889854627)
              ·
                refine ⟨592537505344549334781941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395025003563032889854627 592537505344549334781941)
                ·
                  refine ⟨55550391126051500135807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592537505344549334781941 55550391126051500135807)
                  ·
                    rfl

theorem cell21_243414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_243414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243414 prefixEnd_243414 := by exact prefixLift 243414
  have htrace : WordTrace (prefixWord ++ tailWord_243414) baseStart_243414 baseEnd_243414 := by
    simpa [prefixWord, tailWord_243414, baseEnd_243414] using wordTrace_append hprefix tailTrace_243414
  have hstable : (prefixWord ++ tailWord_243414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243414).length < 2 ^ (prefixWord ++ tailWord_243414).sum := by decide
  have hdescent : baseEnd_243414 < baseStart_243414 := by decide
  rcases family_descends (prefixWord ++ tailWord_243414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243467 : List Nat := [1, 1, 1, 1, 5, 1, 11]
def baseStart_243467 : Nat := 118140960795 + 243467 * 2 ^ 59
def prefixEnd_243467 : Nat := 4983230072969 + 3 ^ 40 * 243467 * 2
def baseEnd_243467 : Nat := 6173609605348353972485

theorem tailTrace_243467 : CollatzResearch.WordTrace tailWord_243467 prefixEnd_243467 6173609605348353972485 := by
  unfold tailWord_243467
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879971008968114698288655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5919980672645409798859103 8879971008968114698288655)
  ·
    refine ⟨13319956513452172047432983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8879971008968114698288655 13319956513452172047432983)
    ·
      refine ⟨19979934770178258071149475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13319956513452172047432983 19979934770178258071149475)
      ·
        refine ⟨29969902155267387106724213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19979934770178258071149475 29969902155267387106724213)
        ·
          refine ⟨2809678327056317541255395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29969902155267387106724213 2809678327056317541255395)
          ·
            refine ⟨4214517490584476311883093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809678327056317541255395 4214517490584476311883093)
            ·
              refine ⟨6173609605348353972485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4214517490584476311883093 6173609605348353972485)
              ·
                rfl

theorem cell21_243467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 11].length) (baseStart_243467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243467 prefixEnd_243467 := by exact prefixLift 243467
  have htrace : WordTrace (prefixWord ++ tailWord_243467) baseStart_243467 baseEnd_243467 := by
    simpa [prefixWord, tailWord_243467, baseEnd_243467] using wordTrace_append hprefix tailTrace_243467
  have hstable : (prefixWord ++ tailWord_243467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243467).length < 2 ^ (prefixWord ++ tailWord_243467).sum := by decide
  have hdescent : baseEnd_243467 < baseStart_243467 := by decide
  rcases family_descends (prefixWord ++ tailWord_243467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243484 : List Nat := [2, 2, 3, 1, 1, 2, 4, 6]
def baseStart_243484 : Nat := 118140960795 + 243484 * 2 ^ 59
def prefixEnd_243484 : Nat := 4983230072969 + 3 ^ 40 * 243484 * 2
def baseEnd_243484 : Nat := 18522122026582311322999

theorem tailTrace_243484 : CollatzResearch.WordTrace tailWord_243484 prefixEnd_243484 18522122026582311322999 := by
  unfold tailWord_243484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440295524953263300828753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5920394033271017734438337 4440295524953263300828753)
  ·
    refine ⟨3330221643714947475621565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4440295524953263300828753 3330221643714947475621565)
    ·
      refine ⟨1248833116393105303358087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3330221643714947475621565 1248833116393105303358087)
      ·
        refine ⟨1873249674589657955037131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248833116393105303358087 1873249674589657955037131)
        ·
          refine ⟨2809874511884486932555697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873249674589657955037131 2809874511884486932555697)
          ·
            refine ⟨2107405883913365199416773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809874511884486932555697 2107405883913365199416773)
            ·
              refine ⟨395138603233755974890645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2107405883913365199416773 395138603233755974890645)
              ·
                refine ⟨18522122026582311322999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 395138603233755974890645 18522122026582311322999)
                ·
                  rfl

theorem cell21_243484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_243484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243484 prefixEnd_243484 := by exact prefixLift 243484
  have htrace : WordTrace (prefixWord ++ tailWord_243484) baseStart_243484 baseEnd_243484 := by
    simpa [prefixWord, tailWord_243484, baseEnd_243484] using wordTrace_append hprefix tailTrace_243484
  have hstable : (prefixWord ++ tailWord_243484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243484).length < 2 ^ (prefixWord ++ tailWord_243484).sum := by decide
  have hdescent : baseEnd_243484 < baseStart_243484 := by decide
  rcases family_descends (prefixWord ++ tailWord_243484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243788 : List Nat := [2, 2, 1, 3, 1, 1, 6, 5]
def baseStart_243788 : Nat := 118140960795 + 243788 * 2 ^ 59
def prefixEnd_243788 : Nat := 4983230072969 + 3 ^ 40 * 243788 * 2
def baseEnd_243788 : Nat := 18545247673836653633903

theorem tailTrace_243788 : CollatzResearch.WordTrace tailWord_243788 prefixEnd_243788 18545247673836653633903 := by
  unfold tailWord_243788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445839420402593260362009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5927785893870124347149345 4445839420402593260362009)
  ·
    refine ⟨3334379565301944945271507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4445839420402593260362009 3334379565301944945271507)
    ·
      refine ⟨5001569347952917417907261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334379565301944945271507 5001569347952917417907261)
      ·
        refine ⟨1875588505482344031715223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5001569347952917417907261 1875588505482344031715223)
        ·
          refine ⟨2813382758223516047572835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875588505482344031715223 2813382758223516047572835)
          ·
            refine ⟨4220074137335274071359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813382758223516047572835 4220074137335274071359253)
            ·
              refine ⟨197815975187590972094965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4220074137335274071359253 197815975187590972094965)
              ·
                refine ⟨18545247673836653633903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197815975187590972094965 18545247673836653633903)
                ·
                  rfl

theorem cell21_243788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_243788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243788 prefixEnd_243788 := by exact prefixLift 243788
  have htrace : WordTrace (prefixWord ++ tailWord_243788) baseStart_243788 baseEnd_243788 := by
    simpa [prefixWord, tailWord_243788, baseEnd_243788] using wordTrace_append hprefix tailTrace_243788
  have hstable : (prefixWord ++ tailWord_243788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243788).length < 2 ^ (prefixWord ++ tailWord_243788).sum := by decide
  have hdescent : baseEnd_243788 < baseStart_243788 := by decide
  rcases family_descends (prefixWord ++ tailWord_243788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243794 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_243794 : Nat := 118140960795 + 243794 * 2 ^ 59
def prefixEnd_243794 : Nat := 4983230072969 + 3 ^ 40 * 243794 * 2
def baseEnd_243794 : Nat := 55637112303255283801697

theorem tailTrace_243794 : CollatzResearch.WordTrace tailWord_243794 prefixEnd_243794 55637112303255283801697 := by
  unfold tailWord_243794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222974419695862386360609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5927931785855633030294957 2222974419695862386360609)
  ·
    refine ⟨1667230814771896789770457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2222974419695862386360609 1667230814771896789770457)
    ·
      refine ⟨1250423111078922592327843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667230814771896789770457 1250423111078922592327843)
      ·
        refine ⟨1875634666618383888491765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250423111078922592327843 1875634666618383888491765)
        ·
          refine ⟨175840749995473489546103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1875634666618383888491765 175840749995473489546103)
          ·
            refine ⟨263761124993210234319155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175840749995473489546103 263761124993210234319155)
            ·
              refine ⟨395641687489815351478733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263761124993210234319155 395641687489815351478733)
              ·
                refine ⟨148365632808680756804525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395641687489815351478733 148365632808680756804525)
                ·
                  refine ⟨55637112303255283801697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148365632808680756804525 55637112303255283801697)
                  ·
                    rfl

theorem cell21_243794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_243794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243794 prefixEnd_243794 := by exact prefixLift 243794
  have htrace : WordTrace (prefixWord ++ tailWord_243794) baseStart_243794 baseEnd_243794 := by
    simpa [prefixWord, tailWord_243794, baseEnd_243794] using wordTrace_append hprefix tailTrace_243794
  have hstable : (prefixWord ++ tailWord_243794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243794).length < 2 ^ (prefixWord ++ tailWord_243794).sum := by decide
  have hdescent : baseEnd_243794 < baseStart_243794 := by decide
  rcases family_descends (prefixWord ++ tailWord_243794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243805 : List Nat := [1, 4, 4, 1, 1, 3, 7]
def baseStart_243805 : Nat := 118140960795 + 243805 * 2 ^ 59
def prefixEnd_243805 : Nat := 4983230072969 + 3 ^ 40 * 243805 * 2
def baseEnd_243805 : Nat := 6182180294791301013149

theorem tailTrace_243805 : CollatzResearch.WordTrace tailWord_243805 prefixEnd_243805 6182180294791301013149 := by
  unfold tailWord_243805
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892298881743598424092869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5928199254495732282728579 8892298881743598424092869)
  ·
    refine ⟨1667306040326924704517413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8892298881743598424092869 1667306040326924704517413)
    ·
      refine ⟨312619882561298382097015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1667306040326924704517413 312619882561298382097015)
      ·
        refine ⟨468929823841947573145523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312619882561298382097015 468929823841947573145523)
        ·
          refine ⟨703394735762921359718285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468929823841947573145523 703394735762921359718285)
          ·
            refine ⟨263773025911095509894357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703394735762921359718285 263773025911095509894357)
            ·
              refine ⟨6182180294791301013149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263773025911095509894357 6182180294791301013149)
              ·
                rfl

theorem cell21_243805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 7].length) (baseStart_243805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243805 prefixEnd_243805 := by exact prefixLift 243805
  have htrace : WordTrace (prefixWord ++ tailWord_243805) baseStart_243805 baseEnd_243805 := by
    simpa [prefixWord, tailWord_243805, baseEnd_243805] using wordTrace_append hprefix tailTrace_243805
  have hstable : (prefixWord ++ tailWord_243805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243805).length < 2 ^ (prefixWord ++ tailWord_243805).sum := by decide
  have hdescent : baseEnd_243805 < baseStart_243805 := by decide
  rcases family_descends (prefixWord ++ tailWord_243805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243847 : List Nat := [1, 1, 4, 2, 1, 1, 4, 7]
def baseStart_243847 : Nat := 118140960795 + 243847 * 2 ^ 59
def prefixEnd_243847 : Nat := 4983230072969 + 3 ^ 40 * 243847 * 2
def baseEnd_243847 : Nat := 18549735875112989806085

theorem tailTrace_243847 : CollatzResearch.WordTrace tailWord_243847 prefixEnd_243847 18549735875112989806085 := by
  unfold tailWord_243847
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893830747591439597121795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5929220498394293064747863 8893830747591439597121795)
  ·
    refine ⟨13340746121387159395682693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8893830747591439597121795 13340746121387159395682693)
    ·
      refine ⟨2501389897760092386690505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13340746121387159395682693 2501389897760092386690505)
      ·
        refine ⟨1876042423320069290017879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2501389897760092386690505 1876042423320069290017879)
        ·
          refine ⟨2814063634980103935026819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876042423320069290017879 2814063634980103935026819)
          ·
            refine ⟨4221095452470155902540229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814063634980103935026819 4221095452470155902540229)
            ·
              refine ⟨791455397338154231726293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4221095452470155902540229 791455397338154231726293)
              ·
                refine ⟨18549735875112989806085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 791455397338154231726293 18549735875112989806085)
                ·
                  rfl

theorem cell21_243847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_243847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243847 prefixEnd_243847 := by exact prefixLift 243847
  have htrace : WordTrace (prefixWord ++ tailWord_243847) baseStart_243847 baseEnd_243847 := by
    simpa [prefixWord, tailWord_243847, baseEnd_243847] using wordTrace_append hprefix tailTrace_243847
  have hstable : (prefixWord ++ tailWord_243847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243847).length < 2 ^ (prefixWord ++ tailWord_243847).sum := by decide
  have hdescent : baseEnd_243847 < baseStart_243847 := by decide
  rcases family_descends (prefixWord ++ tailWord_243847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243862 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_243862 : Nat := 118140960795 + 243862 * 2 ^ 59
def prefixEnd_243862 : Nat := 4983230072969 + 3 ^ 40 * 243862 * 2
def baseEnd_243862 : Nat := 55652630829702276668225

theorem tailTrace_243862 : CollatzResearch.WordTrace tailWord_243862 prefixEnd_243862 55652630829702276668225 := by
  unfold tailWord_243862
  simp only [CollatzResearch.WordTrace]
  refine ⟨555898615158568572432365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5929585228358064772611893 555898615158568572432365)
  ·
    refine ⟨208461980684463214662137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 555898615158568572432365 208461980684463214662137)
    ·
      refine ⟨156346485513347410996603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208461980684463214662137 156346485513347410996603)
      ·
        refine ⟨234519728270021116494905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156346485513347410996603 234519728270021116494905)
        ·
          refine ⟨175889796202515837371179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234519728270021116494905 175889796202515837371179)
          ·
            refine ⟨263834694303773756056769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175889796202515837371179 263834694303773756056769)
            ·
              refine ⟨197876020727830317042577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263834694303773756056769 197876020727830317042577)
              ·
                refine ⟨148407015545872737781933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197876020727830317042577 148407015545872737781933)
                ·
                  refine ⟨55652630829702276668225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148407015545872737781933 55652630829702276668225)
                  ·
                    rfl

theorem cell21_243862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_243862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243862 prefixEnd_243862 := by exact prefixLift 243862
  have htrace : WordTrace (prefixWord ++ tailWord_243862) baseStart_243862 baseEnd_243862 := by
    simpa [prefixWord, tailWord_243862, baseEnd_243862] using wordTrace_append hprefix tailTrace_243862
  have hstable : (prefixWord ++ tailWord_243862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243862).length < 2 ^ (prefixWord ++ tailWord_243862).sum := by decide
  have hdescent : baseEnd_243862 < baseStart_243862 := by decide
  rcases family_descends (prefixWord ++ tailWord_243862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243864 : List Nat := [2, 1, 2, 4, 4, 8]
def baseStart_243864 : Nat := 118140960795 + 243864 * 2 ^ 59
def prefixEnd_243864 : Nat := 4983230072969 + 3 ^ 40 * 243864 * 2
def baseEnd_243864 : Nat := 2061225453961137690181

theorem tailTrace_243864 : CollatzResearch.WordTrace tailWord_243864 prefixEnd_243864 2061225453961137690181 := by
  unfold tailWord_243864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447225394264925750245323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5929633859019901000327097 4447225394264925750245323)
  ·
    refine ⟨6670838091397388625367985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447225394264925750245323 6670838091397388625367985)
    ·
      refine ⟨5003128568548041469025989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6670838091397388625367985 5003128568548041469025989)
      ·
        refine ⟨938086606602757775442373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5003128568548041469025989 938086606602757775442373)
        ·
          refine ⟨175891238738017082895445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 938086606602757775442373 175891238738017082895445)
          ·
            refine ⟨2061225453961137690181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 175891238738017082895445 2061225453961137690181)
            ·
              rfl

theorem cell21_243864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 8].length) (baseStart_243864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243864 prefixEnd_243864 := by exact prefixLift 243864
  have htrace : WordTrace (prefixWord ++ tailWord_243864) baseStart_243864 baseEnd_243864 := by
    simpa [prefixWord, tailWord_243864, baseEnd_243864] using wordTrace_append hprefix tailTrace_243864
  have hstable : (prefixWord ++ tailWord_243864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243864).length < 2 ^ (prefixWord ++ tailWord_243864).sum := by decide
  have hdescent : baseEnd_243864 < baseStart_243864 := by decide
  rcases family_descends (prefixWord ++ tailWord_243864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243943 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 4]
def baseStart_243943 : Nat := 118140960795 + 243943 * 2 ^ 59
def prefixEnd_243943 : Nat := 4983230072969 + 3 ^ 40 * 243943 * 2
def baseEnd_243943 : Nat := 55671116133264135818059

theorem tailTrace_243943 : CollatzResearch.WordTrace tailWord_243943 prefixEnd_243943 55671116133264135818059 := by
  unfold tailWord_243943
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897332155243647992616483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5931554770162431995077655 8897332155243647992616483)
  ·
    refine ⟨13345998232865471988924725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8897332155243647992616483 13345998232865471988924725)
    ·
      refine ⟨1251187334331137998961693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13345998232865471988924725 1251187334331137998961693)
      ·
        refine ⟨469195250374176749610635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1251187334331137998961693 469195250374176749610635)
        ·
          refine ⟨703792875561265124415953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469195250374176749610635 703792875561265124415953)
          ·
            refine ⟨527844656670948843311965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703792875561265124415953 527844656670948843311965)
            ·
              refine ⟨197941746251605816241987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527844656670948843311965 197941746251605816241987)
              ·
                refine ⟨296912619377408724362981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197941746251605816241987 296912619377408724362981)
                ·
                  refine ⟨55671116133264135818059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296912619377408724362981 55671116133264135818059)
                  ·
                    rfl

theorem cell21_243943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4].length) (baseStart_243943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243943 prefixEnd_243943 := by exact prefixLift 243943
  have htrace : WordTrace (prefixWord ++ tailWord_243943) baseStart_243943 baseEnd_243943 := by
    simpa [prefixWord, tailWord_243943, baseEnd_243943] using wordTrace_append hprefix tailTrace_243943
  have hstable : (prefixWord ++ tailWord_243943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243943).length < 2 ^ (prefixWord ++ tailWord_243943).sum := by decide
  have hdescent : baseEnd_243943 < baseStart_243943 := by decide
  rcases family_descends (prefixWord ++ tailWord_243943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243968 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_243968 : Nat := 118140960795 + 243968 * 2 ^ 59
def prefixEnd_243968 : Nat := 4983230072969 + 3 ^ 40 * 243968 * 2
def baseEnd_243968 : Nat := 55676821473869647901341

theorem tailTrace_243968 : CollatzResearch.WordTrace tailWord_243968 prefixEnd_243968 55676821473869647901341 := by
  unfold tailWord_243968
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449121990076538631138279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5932162653435384841517705 4449121990076538631138279)
  ·
    refine ⟨6673682985114807946707419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4449121990076538631138279 6673682985114807946707419)
    ·
      refine ⟨10010524477672211920061129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6673682985114807946707419 10010524477672211920061129)
      ·
        refine ⟨7507893358254158940045847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10010524477672211920061129 7507893358254158940045847)
        ·
          refine ⟨11261840037381238410068771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7507893358254158940045847 11261840037381238410068771)
          ·
            refine ⟨16892760056071857615103157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261840037381238410068771 16892760056071857615103157)
            ·
              refine ⟨1583696255256736651415921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16892760056071857615103157 1583696255256736651415921)
              ·
                refine ⟨1187772191442552488561941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583696255256736651415921 1187772191442552488561941)
                ·
                  refine ⟨55676821473869647901341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1187772191442552488561941 55676821473869647901341)
                  ·
                    rfl

theorem cell21_243968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_243968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243968 prefixEnd_243968 := by exact prefixLift 243968
  have htrace : WordTrace (prefixWord ++ tailWord_243968) baseStart_243968 baseEnd_243968 := by
    simpa [prefixWord, tailWord_243968, baseEnd_243968] using wordTrace_append hprefix tailTrace_243968
  have hstable : (prefixWord ++ tailWord_243968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243968).length < 2 ^ (prefixWord ++ tailWord_243968).sum := by decide
  have hdescent : baseEnd_243968 < baseStart_243968 := by decide
  rcases family_descends (prefixWord ++ tailWord_243968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243999 : List Nat := [1, 1, 2, 4, 3, 1, 1, 8]
def baseStart_243999 : Nat := 118140960795 + 243999 * 2 ^ 59
def prefixEnd_243999 : Nat := 4983230072969 + 3 ^ 40 * 243999 * 2
def baseEnd_243999 : Nat := 18561298698740160961537

theorem tailTrace_243999 : CollatzResearch.WordTrace tailWord_243999 prefixEnd_243999 18561298698740160961537 := by
  unfold tailWord_243999
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899374643040769556655051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5932916428693846371103367 8899374643040769556655051)
  ·
    refine ⟨13349061964561154334982577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8899374643040769556655051 13349061964561154334982577)
    ·
      refine ⟨10011796473420865751236933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13349061964561154334982577 10011796473420865751236933)
      ·
        refine ⟨1877211838766412328356925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10011796473420865751236933 1877211838766412328356925)
        ·
          refine ⟨703954439537404623133847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1877211838766412328356925 703954439537404623133847)
          ·
            refine ⟨1055931659306106934700771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703954439537404623133847 1055931659306106934700771)
            ·
              refine ⟨1583897488959160402051157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055931659306106934700771 1583897488959160402051157)
              ·
                refine ⟨18561298698740160961537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1583897488959160402051157 18561298698740160961537)
                ·
                  rfl

theorem cell21_243999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_243999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_243999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_243999 prefixEnd_243999 := by exact prefixLift 243999
  have htrace : WordTrace (prefixWord ++ tailWord_243999) baseStart_243999 baseEnd_243999 := by
    simpa [prefixWord, tailWord_243999, baseEnd_243999] using wordTrace_append hprefix tailTrace_243999
  have hstable : (prefixWord ++ tailWord_243999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243999).length < 2 ^ (prefixWord ++ tailWord_243999).sum := by decide
  have hdescent : baseEnd_243999 < baseStart_243999 := by decide
  rcases family_descends (prefixWord ++ tailWord_243999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244002 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_244002 : Nat := 118140960795 + 244002 * 2 ^ 59
def prefixEnd_244002 : Nat := 4983230072969 + 3 ^ 40 * 244002 * 2
def baseEnd_244002 : Nat := 55684580737093144334605

theorem tailTrace_244002 : CollatzResearch.WordTrace tailWord_244002 prefixEnd_244002 55684580737093144334605 := by
  unfold tailWord_244002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224871015507475267253565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5932989374686600712676173 2224871015507475267253565)
  ·
    refine ⟨834326630815303225220087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2224871015507475267253565 834326630815303225220087)
    ·
      refine ⟨1251489946222954837830131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834326630815303225220087 1251489946222954837830131)
      ·
        refine ⟨1877234919334432256745197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251489946222954837830131 1877234919334432256745197)
        ·
          refine ⟨703963094750412096279449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1877234919334432256745197 703963094750412096279449)
          ·
            refine ⟨527972321062809072209587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703963094750412096279449 527972321062809072209587)
            ·
              refine ⟨791958481594213608314381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527972321062809072209587 791958481594213608314381)
              ·
                refine ⟨296984430597830103117893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 791958481594213608314381 296984430597830103117893)
                ·
                  refine ⟨55684580737093144334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296984430597830103117893 55684580737093144334605)
                  ·
                    rfl

theorem cell21_244002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_244002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244002 prefixEnd_244002 := by exact prefixLift 244002
  have htrace : WordTrace (prefixWord ++ tailWord_244002) baseStart_244002 baseEnd_244002 := by
    simpa [prefixWord, tailWord_244002, baseEnd_244002] using wordTrace_append hprefix tailTrace_244002
  have hstable : (prefixWord ++ tailWord_244002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244002).length < 2 ^ (prefixWord ++ tailWord_244002).sum := by decide
  have hdescent : baseEnd_244002 < baseStart_244002 := by decide
  rcases family_descends (prefixWord ++ tailWord_244002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244089 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_244089 : Nat := 118140960795 + 244089 * 2 ^ 59
def prefixEnd_244089 : Nat := 4983230072969 + 3 ^ 40 * 244089 * 2
def baseEnd_244089 : Nat := 55704435322400326384427

theorem tailTrace_244089 : CollatzResearch.WordTrace tailWord_244089 prefixEnd_244089 55704435322400326384427 := by
  unfold tailWord_244089
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902657212714714927431321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5935104808476476618287547 8902657212714714927431321)
  ·
    refine ⟨6676992909536036195573491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8902657212714714927431321 6676992909536036195573491)
    ·
      refine ⟨10015489364304054293360237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676992909536036195573491 10015489364304054293360237)
      ·
        refine ⟨3755808511614020360010089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10015489364304054293360237 3755808511614020360010089)
        ·
          refine ⟨2816856383710515270007567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755808511614020360010089 2816856383710515270007567)
          ·
            refine ⟨4225284575565772905011351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816856383710515270007567 4225284575565772905011351)
            ·
              refine ⟨6337926863348659357517027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225284575565772905011351 6337926863348659357517027)
              ·
                refine ⟨9506890295022989036275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337926863348659357517027 9506890295022989036275541)
                ·
                  refine ⟨55704435322400326384427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9506890295022989036275541 55704435322400326384427)
                  ·
                    rfl

theorem cell21_244089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_244089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244089 prefixEnd_244089 := by exact prefixLift 244089
  have htrace : WordTrace (prefixWord ++ tailWord_244089) baseStart_244089 baseEnd_244089 := by
    simpa [prefixWord, tailWord_244089, baseEnd_244089] using wordTrace_append hprefix tailTrace_244089
  have hstable : (prefixWord ++ tailWord_244089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244089).length < 2 ^ (prefixWord ++ tailWord_244089).sum := by decide
  have hdescent : baseEnd_244089 < baseStart_244089 := by decide
  rcases family_descends (prefixWord ++ tailWord_244089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244126 : List Nat := [4, 3, 1, 2, 1, 3, 2, 5]
def baseStart_244126 : Nat := 118140960795 + 244126 * 2 ^ 59
def prefixEnd_244126 : Nat := 4983230072969 + 3 ^ 40 * 244126 * 2
def baseEnd_244126 : Nat := 18570959742165494755895

theorem tailTrace_244126 : CollatzResearch.WordTrace tailWord_244126 prefixEnd_244126 18570959742165494755895 := by
  unfold tailWord_244126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113000839197583780816029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5936004475720446831018821 1113000839197583780816029)
  ·
    refine ⟨417375314699093917806011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1113000839197583780816029 417375314699093917806011)
    ·
      refine ⟨626062972048640876709017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417375314699093917806011 626062972048640876709017)
      ·
        refine ⟨469547229036480657531763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626062972048640876709017 469547229036480657531763)
        ·
          refine ⟨704320843554720986297645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469547229036480657531763 704320843554720986297645)
          ·
            refine ⟨264120316333020369861617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 704320843554720986297645 264120316333020369861617)
            ·
              refine ⟨198090237249765277396213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264120316333020369861617 198090237249765277396213)
              ·
                refine ⟨18570959742165494755895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198090237249765277396213 18570959742165494755895)
                ·
                  rfl

theorem cell21_244126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_244126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244126 prefixEnd_244126 := by exact prefixLift 244126
  have htrace : WordTrace (prefixWord ++ tailWord_244126) baseStart_244126 baseEnd_244126 := by
    simpa [prefixWord, tailWord_244126, baseEnd_244126] using wordTrace_append hprefix tailTrace_244126
  have hstable : (prefixWord ++ tailWord_244126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244126).length < 2 ^ (prefixWord ++ tailWord_244126).sum := by decide
  have hdescent : baseEnd_244126 < baseStart_244126 := by decide
  rcases family_descends (prefixWord ++ tailWord_244126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244151 : List Nat := [1, 1, 3, 1, 3, 5, 7]
def baseStart_244151 : Nat := 118140960795 + 244151 * 2 ^ 59
def prefixEnd_244151 : Nat := 4983230072969 + 3 ^ 40 * 244151 * 2
def baseEnd_244151 : Nat := 6190953840789110705663

theorem tailTrace_244151 : CollatzResearch.WordTrace tailWord_244151 prefixEnd_244151 6190953840789110705663 := by
  unfold tailWord_244151
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904918538490099516188307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5936612358993399677458871 8904918538490099516188307)
  ·
    refine ⟨13357377807735149274282461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8904918538490099516188307 13357377807735149274282461)
    ·
      refine ⟨5009016677900680977855923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13357377807735149274282461 5009016677900680977855923)
      ·
        refine ⟨7513525016851021466783885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009016677900680977855923 7513525016851021466783885)
        ·
          refine ⟨2817571881319133050043957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7513525016851021466783885 2817571881319133050043957)
          ·
            refine ⟨264147363873668723441621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2817571881319133050043957 264147363873668723441621)
            ·
              refine ⟨6190953840789110705663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 264147363873668723441621 6190953840789110705663)
              ·
                rfl

theorem cell21_244151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 7].length) (baseStart_244151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244151 prefixEnd_244151 := by exact prefixLift 244151
  have htrace : WordTrace (prefixWord ++ tailWord_244151) baseStart_244151 baseEnd_244151 := by
    simpa [prefixWord, tailWord_244151, baseEnd_244151] using wordTrace_append hprefix tailTrace_244151
  have hstable : (prefixWord ++ tailWord_244151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244151).length < 2 ^ (prefixWord ++ tailWord_244151).sum := by decide
  have hdescent : baseEnd_244151 < baseStart_244151 := by decide
  rcases family_descends (prefixWord ++ tailWord_244151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244199 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 3]
def baseStart_244199 : Nat := 118140960795 + 244199 * 2 ^ 59
def prefixEnd_244199 : Nat := 4983230072969 + 3 ^ 40 * 244199 * 2
def baseEnd_244199 : Nat := 55729538821064579550869

theorem tailTrace_244199 : CollatzResearch.WordTrace tailWord_244199 prefixEnd_244199 55729538821064579550869 := by
  unfold tailWord_244199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906669242316203713935651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5937779494877469142623767 8906669242316203713935651)
  ·
    refine ⟨13360003863474305570903477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8906669242316203713935651 13360003863474305570903477)
    ·
      refine ⟨1252500362200716147272201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13360003863474305570903477 1252500362200716147272201)
      ·
        refine ⟨939375271650537110454151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1252500362200716147272201 939375271650537110454151)
        ·
          refine ⟨1409062907475805665681227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939375271650537110454151 1409062907475805665681227)
          ·
            refine ⟨2113594361213708498521841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409062907475805665681227 2113594361213708498521841)
            ·
              refine ⟨1585195770910281373891381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113594361213708498521841 1585195770910281373891381)
              ·
                refine ⟨148612103522838878802317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1585195770910281373891381 148612103522838878802317)
                ·
                  refine ⟨55729538821064579550869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148612103522838878802317 55729538821064579550869)
                  ·
                    rfl

theorem cell21_244199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3].length) (baseStart_244199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244199 prefixEnd_244199 := by exact prefixLift 244199
  have htrace : WordTrace (prefixWord ++ tailWord_244199) baseStart_244199 baseEnd_244199 := by
    simpa [prefixWord, tailWord_244199, baseEnd_244199] using wordTrace_append hprefix tailTrace_244199
  have hstable : (prefixWord ++ tailWord_244199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244199).length < 2 ^ (prefixWord ++ tailWord_244199).sum := by decide
  have hdescent : baseEnd_244199 < baseStart_244199 := by decide
  rcases family_descends (prefixWord ++ tailWord_244199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244303 : List Nat := [1, 1, 2, 1, 1, 2, 8, 5]
def baseStart_244303 : Nat := 118140960795 + 244303 * 2 ^ 59
def prefixEnd_244303 : Nat := 4983230072969 + 3 ^ 40 * 244303 * 2
def baseEnd_244303 : Nat := 18584424345994503272441

theorem tailTrace_244303 : CollatzResearch.WordTrace tailWord_244303 prefixEnd_244303 18584424345994503272441 := by
  unfold tailWord_244303
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910462433939429475721563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5940308289292952983814375 8910462433939429475721563)
  ·
    refine ⟨13365693650909144213582345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8910462433939429475721563 13365693650909144213582345)
    ·
      refine ⟨10024270238181858160186759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13365693650909144213582345 10024270238181858160186759)
      ·
        refine ⟨15036405357272787240280139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10024270238181858160186759 15036405357272787240280139)
        ·
          refine ⟨22554608035909180860420209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15036405357272787240280139 22554608035909180860420209)
          ·
            refine ⟨16915956026931885645315157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22554608035909180860420209 16915956026931885645315157)
            ·
              refine ⟨198233859690608034906037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 16915956026931885645315157 198233859690608034906037)
              ·
                refine ⟨18584424345994503272441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198233859690608034906037 18584424345994503272441)
                ·
                  rfl

theorem cell21_244303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 5].length) (baseStart_244303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244303 prefixEnd_244303 := by exact prefixLift 244303
  have htrace : WordTrace (prefixWord ++ tailWord_244303) baseStart_244303 baseEnd_244303 := by
    simpa [prefixWord, tailWord_244303, baseEnd_244303] using wordTrace_append hprefix tailTrace_244303
  have hstable : (prefixWord ++ tailWord_244303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244303).length < 2 ^ (prefixWord ++ tailWord_244303).sum := by decide
  have hdescent : baseEnd_244303 < baseStart_244303 := by decide
  rcases family_descends (prefixWord ++ tailWord_244303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244382 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_244382 : Nat := 118140960795 + 244382 * 2 ^ 59
def prefixEnd_244382 : Nat := 4983230072969 + 3 ^ 40 * 244382 * 2
def baseEnd_244382 : Nat := 55771301914296928000495

theorem tailTrace_244382 : CollatzResearch.WordTrace tailWord_244382 prefixEnd_244382 55771301914296928000495 := by
  unfold tailWord_244382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114167975081653245980925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5942229200435483978564933 1114167975081653245980925)
  ·
    refine ⟨417812990655619967242847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1114167975081653245980925 417812990655619967242847)
    ·
      refine ⟨626719485983429950864271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417812990655619967242847 626719485983429950864271)
      ·
        refine ⟨940079228975144926296407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626719485983429950864271 940079228975144926296407)
        ·
          refine ⟨1410118843462717389444611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940079228975144926296407 1410118843462717389444611)
          ·
            refine ⟨2115178265194076084166917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410118843462717389444611 2115178265194076084166917)
            ·
              refine ⟨396595924723889265781297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2115178265194076084166917 396595924723889265781297)
              ·
                refine ⟨297446943542916949335973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396595924723889265781297 297446943542916949335973)
                ·
                  refine ⟨55771301914296928000495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297446943542916949335973 55771301914296928000495)
                  ·
                    rfl

theorem cell21_244382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_244382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244382 prefixEnd_244382 := by exact prefixLift 244382
  have htrace : WordTrace (prefixWord ++ tailWord_244382) baseStart_244382 baseEnd_244382 := by
    simpa [prefixWord, tailWord_244382, baseEnd_244382] using wordTrace_append hprefix tailTrace_244382
  have hstable : (prefixWord ++ tailWord_244382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244382).length < 2 ^ (prefixWord ++ tailWord_244382).sum := by decide
  have hdescent : baseEnd_244382 < baseStart_244382 := by decide
  rcases family_descends (prefixWord ++ tailWord_244382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244385 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 3]
def baseStart_244385 : Nat := 118140960795 + 244385 * 2 ^ 59
def prefixEnd_244385 : Nat := 4983230072969 + 3 ^ 40 * 244385 * 2
def baseEnd_244385 : Nat := 55771986555169589450489

theorem tailTrace_244385 : CollatzResearch.WordTrace tailWord_244385 prefixEnd_244385 55771986555169589450489 := by
  unfold tailWord_244385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913453219642357480206609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5942302146428238320137739 8913453219642357480206609)
  ·
    refine ⟨6685089914731768110154957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8913453219642357480206609 6685089914731768110154957)
    ·
      refine ⟨2506908718024413041308109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6685089914731768110154957 2506908718024413041308109)
      ·
        refine ⟨940090769259154890490541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2506908718024413041308109 940090769259154890490541)
        ·
          refine ⟨352534038472183083933953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940090769259154890490541 352534038472183083933953)
          ·
            refine ⟨264400528854137312950465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352534038472183083933953 264400528854137312950465)
            ·
              refine ⟨198300396640602984712849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264400528854137312950465 198300396640602984712849)
              ·
                refine ⟨148725297480452238534637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198300396640602984712849 148725297480452238534637)
                ·
                  refine ⟨55771986555169589450489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148725297480452238534637 55771986555169589450489)
                  ·
                    rfl

theorem cell21_244385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_244385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244385 prefixEnd_244385 := by exact prefixLift 244385
  have htrace : WordTrace (prefixWord ++ tailWord_244385) baseStart_244385 baseEnd_244385 := by
    simpa [prefixWord, tailWord_244385, baseEnd_244385] using wordTrace_append hprefix tailTrace_244385
  have hstable : (prefixWord ++ tailWord_244385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244385).length < 2 ^ (prefixWord ++ tailWord_244385).sum := by decide
  have hdescent : baseEnd_244385 < baseStart_244385 := by decide
  rcases family_descends (prefixWord ++ tailWord_244385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244444 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_244444 : Nat := 118140960795 + 244444 * 2 ^ 59
def prefixEnd_244444 : Nat := 4983230072969 + 3 ^ 40 * 244444 * 2
def baseEnd_244444 : Nat := 55785451158998597967035

theorem tailTrace_244444 : CollatzResearch.WordTrace tailWord_244444 prefixEnd_244444 55785451158998597967035 := by
  unfold tailWord_244444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4457802563214305278302193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5943736750952407037736257 4457802563214305278302193)
  ·
    refine ⟨3343351922410728958726645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4457802563214305278302193 3343351922410728958726645)
    ·
      refine ⟨313439242726005839880623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3343351922410728958726645 313439242726005839880623)
      ·
        refine ⟨470158864089008759820935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313439242726005839880623 470158864089008759820935)
        ·
          refine ⟨705238296133513139731403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470158864089008759820935 705238296133513139731403)
          ·
            refine ⟨1057857444200269709597105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705238296133513139731403 1057857444200269709597105)
            ·
              refine ⟨793393083150202282197829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057857444200269709597105 793393083150202282197829)
              ·
                refine ⟨148761203090662927912093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793393083150202282197829 148761203090662927912093)
                ·
                  refine ⟨55785451158998597967035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148761203090662927912093 55785451158998597967035)
                  ·
                    rfl

theorem cell21_244444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_244444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244444 prefixEnd_244444 := by exact prefixLift 244444
  have htrace : WordTrace (prefixWord ++ tailWord_244444) baseStart_244444 baseEnd_244444 := by
    simpa [prefixWord, tailWord_244444, baseEnd_244444] using wordTrace_append hprefix tailTrace_244444
  have hstable : (prefixWord ++ tailWord_244444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244444).length < 2 ^ (prefixWord ++ tailWord_244444).sum := by decide
  have hdescent : baseEnd_244444 < baseStart_244444 := by decide
  rcases family_descends (prefixWord ++ tailWord_244444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244503 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 5]
def baseStart_244503 : Nat := 118140960795 + 244503 * 2 ^ 59
def prefixEnd_244503 : Nat := 4983230072969 + 3 ^ 40 * 244503 * 2
def baseEnd_244503 : Nat := 55798915762827606483581

theorem tailTrace_244503 : CollatzResearch.WordTrace tailWord_244503 prefixEnd_244503 55798915762827606483581 := by
  unfold tailWord_244503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917757033214863633002163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5945171355476575755334775 8917757033214863633002163)
  ·
    refine ⟨13376635549822295449503245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8917757033214863633002163 13376635549822295449503245)
    ·
      refine ⟨5016238331183360793563717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13376635549822295449503245 5016238331183360793563717)
      ·
        refine ⟨940544687096880148793197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5016238331183360793563717 940544687096880148793197)
        ·
          refine ⟨352704257661330055797449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 940544687096880148793197 352704257661330055797449)
          ·
            refine ⟨264528193245997541848087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352704257661330055797449 264528193245997541848087)
            ·
              refine ⟨396792289868996312772131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264528193245997541848087 396792289868996312772131)
              ·
                refine ⟨595188434803494469158197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396792289868996312772131 595188434803494469158197)
                ·
                  refine ⟨55798915762827606483581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595188434803494469158197 55798915762827606483581)
                  ·
                    rfl

theorem cell21_244503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 5].length) (baseStart_244503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244503 prefixEnd_244503 := by exact prefixLift 244503
  have htrace : WordTrace (prefixWord ++ tailWord_244503) baseStart_244503 baseEnd_244503 := by
    simpa [prefixWord, tailWord_244503, baseEnd_244503] using wordTrace_append hprefix tailTrace_244503
  have hstable : (prefixWord ++ tailWord_244503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244503).length < 2 ^ (prefixWord ++ tailWord_244503).sum := by decide
  have hdescent : baseEnd_244503 < baseStart_244503 := by decide
  rcases family_descends (prefixWord ++ tailWord_244503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244548 : List Nat := [2, 3, 4, 2, 1, 9]
def baseStart_244548 : Nat := 118140960795 + 244548 * 2 ^ 59
def prefixEnd_244548 : Nat := 4983230072969 + 3 ^ 40 * 244548 * 2
def baseEnd_244548 : Nat := 2067006865774723267907

theorem tailTrace_244548 : CollatzResearch.WordTrace tailWord_244548 prefixEnd_244548 2067006865774723267907 := by
  unfold tailWord_244548
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459699159025918159195149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5946265545367890878926865 4459699159025918159195149)
  ·
    refine ⟨1672387184634719309698181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4459699159025918159195149 1672387184634719309698181)
    ·
      refine ⟨313572597119009870568409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1672387184634719309698181 313572597119009870568409)
      ·
        refine ⟨235179447839257402926307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313572597119009870568409 235179447839257402926307)
        ·
          refine ⟨352769171758886104389461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235179447839257402926307 352769171758886104389461)
          ·
            refine ⟨2067006865774723267907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 352769171758886104389461 2067006865774723267907)
            ·
              rfl

theorem cell21_244548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 9].length) (baseStart_244548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244548 prefixEnd_244548 := by exact prefixLift 244548
  have htrace : WordTrace (prefixWord ++ tailWord_244548) baseStart_244548 baseEnd_244548 := by
    simpa [prefixWord, tailWord_244548, baseEnd_244548] using wordTrace_append hprefix tailTrace_244548
  have hstable : (prefixWord ++ tailWord_244548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244548).length < 2 ^ (prefixWord ++ tailWord_244548).sum := by decide
  have hdescent : baseEnd_244548 < baseStart_244548 := by decide
  rcases family_descends (prefixWord ++ tailWord_244548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244576 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_244576 : Nat := 118140960795 + 244576 * 2 ^ 59
def prefixEnd_244576 : Nat := 4983230072969 + 3 ^ 40 * 244576 * 2
def baseEnd_244576 : Nat := 55815575357395701766765

theorem tailTrace_244576 : CollatzResearch.WordTrace tailWord_244576 prefixEnd_244576 55815575357395701766765 := by
  unfold tailWord_244576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460209780975198550204791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5946946374633598066939721 4460209780975198550204791)
  ·
    refine ⟨6690314671462797825307187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4460209780975198550204791 6690314671462797825307187)
    ·
      refine ⟨10035472007194196737960781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690314671462797825307187 10035472007194196737960781)
      ·
        refine ⟨3763302002697823776735293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10035472007194196737960781 3763302002697823776735293)
        ·
          refine ⟨1411238251011683916275735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3763302002697823776735293 1411238251011683916275735)
          ·
            refine ⟨2116857376517525874413603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411238251011683916275735 2116857376517525874413603)
            ·
              refine ⟨3175286064776288811620405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116857376517525874413603 3175286064776288811620405)
              ·
                refine ⟨297683068572777076089413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3175286064776288811620405 297683068572777076089413)
                ·
                  refine ⟨55815575357395701766765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297683068572777076089413 55815575357395701766765)
                  ·
                    rfl

theorem cell21_244576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_244576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244576 prefixEnd_244576 := by exact prefixLift 244576
  have htrace : WordTrace (prefixWord ++ tailWord_244576) baseStart_244576 baseEnd_244576 := by
    simpa [prefixWord, tailWord_244576, baseEnd_244576] using wordTrace_append hprefix tailTrace_244576
  have hstable : (prefixWord ++ tailWord_244576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244576).length < 2 ^ (prefixWord ++ tailWord_244576).sum := by decide
  have hdescent : baseEnd_244576 < baseStart_244576 := by decide
  rcases family_descends (prefixWord ++ tailWord_244576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244678 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_244678 : Nat := 118140960795 + 244678 * 2 ^ 59
def prefixEnd_244678 : Nat := 4983230072969 + 3 ^ 40 * 244678 * 2
def baseEnd_244678 : Nat := 55838853147066191066557

theorem tailTrace_244678 : CollatzResearch.WordTrace tailWord_244678 prefixEnd_244678 55838853147066191066557 := by
  unfold tailWord_244678
  simp only [CollatzResearch.WordTrace]
  refine ⟨278879368986902141269459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5949426538387245680415125 278879368986902141269459)
  ·
    refine ⟨418319053480353211904189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278879368986902141269459 418319053480353211904189)
    ·
      refine ⟨156869645055132454464071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418319053480353211904189 156869645055132454464071)
      ·
        refine ⟨235304467582698681696107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156869645055132454464071 235304467582698681696107)
        ·
          refine ⟨352956701374048022544161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235304467582698681696107 352956701374048022544161)
          ·
            refine ⟨264717526030536016908121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352956701374048022544161 264717526030536016908121)
            ·
              refine ⟨198538144522902012681091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264717526030536016908121 198538144522902012681091)
              ·
                refine ⟨297807216784353019021637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198538144522902012681091 297807216784353019021637)
                ·
                  refine ⟨55838853147066191066557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297807216784353019021637 55838853147066191066557)
                  ·
                    rfl

theorem cell21_244678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_244678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244678 prefixEnd_244678 := by exact prefixLift 244678
  have htrace : WordTrace (prefixWord ++ tailWord_244678) baseStart_244678 baseEnd_244678 := by
    simpa [prefixWord, tailWord_244678, baseEnd_244678] using wordTrace_append hprefix tailTrace_244678
  have hstable : (prefixWord ++ tailWord_244678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244678).length < 2 ^ (prefixWord ++ tailWord_244678).sum := by decide
  have hdescent : baseEnd_244678 < baseStart_244678 := by decide
  rcases family_descends (prefixWord ++ tailWord_244678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244686 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_244686 : Nat := 118140960795 + 244686 * 2 ^ 59
def prefixEnd_244686 : Nat := 4983230072969 + 3 ^ 40 * 244686 * 2
def baseEnd_244686 : Nat := 55840678856059954933207

theorem tailTrace_244686 : CollatzResearch.WordTrace tailWord_244686 prefixEnd_244686 55840678856059954933207 := by
  unfold tailWord_244686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1115553948943985735864239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5949621061034590591275941 1115553948943985735864239)
  ·
    refine ⟨1673330923415978603796359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1115553948943985735864239 1673330923415978603796359)
    ·
      refine ⟨2509996385123967905694539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1673330923415978603796359 2509996385123967905694539)
      ·
        refine ⟨3764994577685951858541809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509996385123967905694539 3764994577685951858541809)
        ·
          refine ⟨2823745933264463893906357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3764994577685951858541809 2823745933264463893906357)
          ·
            refine ⟨264726181243543490053721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2823745933264463893906357 264726181243543490053721)
            ·
              refine ⟨198544635932657617540291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264726181243543490053721 198544635932657617540291)
              ·
                refine ⟨297816953898986426310437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198544635932657617540291 297816953898986426310437)
                ·
                  refine ⟨55840678856059954933207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297816953898986426310437 55840678856059954933207)
                  ·
                    rfl

theorem cell21_244686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_244686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244686 prefixEnd_244686 := by exact prefixLift 244686
  have htrace : WordTrace (prefixWord ++ tailWord_244686) baseStart_244686 baseEnd_244686 := by
    simpa [prefixWord, tailWord_244686, baseEnd_244686] using wordTrace_append hprefix tailTrace_244686
  have hstable : (prefixWord ++ tailWord_244686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244686).length < 2 ^ (prefixWord ++ tailWord_244686).sum := by decide
  have hdescent : baseEnd_244686 < baseStart_244686 := by decide
  rcases family_descends (prefixWord ++ tailWord_244686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244790 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_244790 : Nat := 118140960795 + 244790 * 2 ^ 59
def prefixEnd_244790 : Nat := 4983230072969 + 3 ^ 40 * 244790 * 2
def baseEnd_244790 : Nat := 55864413072978885199661

theorem tailTrace_244790 : CollatzResearch.WordTrace tailWord_244790 prefixEnd_244790 55864413072978885199661 := by
  unfold tailWord_244790
  simp only [CollatzResearch.WordTrace]
  refine ⟨558014048948444478043739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5952149855450074432466549 558014048948444478043739)
  ·
    refine ⟨837021073422666717065609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558014048948444478043739 837021073422666717065609)
    ·
      refine ⟨627765805067000037799207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837021073422666717065609 627765805067000037799207)
      ·
        refine ⟨941648707600500056698811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627765805067000037799207 941648707600500056698811)
        ·
          refine ⟨1412473061400750085048217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941648707600500056698811 1412473061400750085048217)
          ·
            refine ⟨1059354796050562563786163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412473061400750085048217 1059354796050562563786163)
            ·
              refine ⟨1589032194075843845679245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059354796050562563786163 1589032194075843845679245)
              ·
                refine ⟨595887072778441442129717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589032194075843845679245 595887072778441442129717)
                ·
                  refine ⟨55864413072978885199661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595887072778441442129717 55864413072978885199661)
                  ·
                    rfl

theorem cell21_244790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_244790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244790 prefixEnd_244790 := by exact prefixLift 244790
  have htrace : WordTrace (prefixWord ++ tailWord_244790) baseStart_244790 baseEnd_244790 := by
    simpa [prefixWord, tailWord_244790, baseEnd_244790] using wordTrace_append hprefix tailTrace_244790
  have hstable : (prefixWord ++ tailWord_244790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244790).length < 2 ^ (prefixWord ++ tailWord_244790).sum := by decide
  have hdescent : baseEnd_244790 < baseStart_244790 := by decide
  rcases family_descends (prefixWord ++ tailWord_244790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244900 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_244900 : Nat := 118140960795 + 244900 * 2 ^ 59
def prefixEnd_244900 : Nat := 4983230072969 + 3 ^ 40 * 244900 * 2
def baseEnd_244900 : Nat := 55889516571643138366103

theorem tailTrace_244900 : CollatzResearch.WordTrace tailWord_244900 prefixEnd_244900 55889516571643138366103 := by
  unfold tailWord_244900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466118406388300217602077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5954824541851066956802769 4466118406388300217602077)
  ·
    refine ⟨1674794402395612581600779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4466118406388300217602077 1674794402395612581600779)
    ·
      refine ⟨2512191603593418872401169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674794402395612581600779 2512191603593418872401169)
      ·
        refine ⟨1884143702695064154300877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512191603593418872401169 1884143702695064154300877)
        ·
          refine ⟨706553888510649057862829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1884143702695064154300877 706553888510649057862829)
          ·
            refine ⟨264957708191493396698561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706553888510649057862829 264957708191493396698561)
            ·
              refine ⟨198718281143620047523921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264957708191493396698561 198718281143620047523921)
              ·
                refine ⟨149038710857715035642941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198718281143620047523921 149038710857715035642941)
                ·
                  refine ⟨55889516571643138366103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149038710857715035642941 55889516571643138366103)
                  ·
                    rfl

theorem cell21_244900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_244900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244900 prefixEnd_244900 := by exact prefixLift 244900
  have htrace : WordTrace (prefixWord ++ tailWord_244900) baseStart_244900 baseEnd_244900 := by
    simpa [prefixWord, tailWord_244900, baseEnd_244900] using wordTrace_append hprefix tailTrace_244900
  have hstable : (prefixWord ++ tailWord_244900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244900).length < 2 ^ (prefixWord ++ tailWord_244900).sum := by decide
  have hdescent : baseEnd_244900 < baseStart_244900 := by decide
  rcases family_descends (prefixWord ++ tailWord_244900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244934 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_244934 : Nat := 118140960795 + 244934 * 2 ^ 59
def prefixEnd_244934 : Nat := 4983230072969 + 3 ^ 40 * 244934 * 2
def baseEnd_244934 : Nat := 55897275834866634799367

theorem tailTrace_244934 : CollatzResearch.WordTrace tailWord_244934 prefixEnd_244934 55897275834866634799367 := by
  unfold tailWord_244934
  simp only [CollatzResearch.WordTrace]
  refine ⟨279171152957919507560683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5955651263102282827961237 279171152957919507560683)
  ·
    refine ⟨418756729436879261341025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279171152957919507560683 418756729436879261341025)
    ·
      refine ⟨314067547077659446005769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418756729436879261341025 314067547077659446005769)
      ·
        refine ⟨235550660308244584504327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314067547077659446005769 235550660308244584504327)
        ·
          refine ⟨353325990462366876756491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235550660308244584504327 353325990462366876756491)
          ·
            refine ⟨529988985693550315134737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353325990462366876756491 529988985693550315134737)
            ·
              refine ⟨397491739270162736351053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529988985693550315134737 397491739270162736351053)
              ·
                refine ⟨149059402226311026131645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397491739270162736351053 149059402226311026131645)
                ·
                  refine ⟨55897275834866634799367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149059402226311026131645 55897275834866634799367)
                  ·
                    rfl

theorem cell21_244934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_244934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_244934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_244934 prefixEnd_244934 := by exact prefixLift 244934
  have htrace : WordTrace (prefixWord ++ tailWord_244934) baseStart_244934 baseEnd_244934 := by
    simpa [prefixWord, tailWord_244934, baseEnd_244934] using wordTrace_append hprefix tailTrace_244934
  have hstable : (prefixWord ++ tailWord_244934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244934).length < 2 ^ (prefixWord ++ tailWord_244934).sum := by decide
  have hdescent : baseEnd_244934 < baseStart_244934 := by decide
  rcases family_descends (prefixWord ++ tailWord_244934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245015 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_245015 : Nat := 118140960795 + 245015 * 2 ^ 59
def prefixEnd_245015 : Nat := 4983230072969 + 3 ^ 40 * 245015 * 2
def baseEnd_245015 : Nat := 55915761138428493949201

theorem tailTrace_245015 : CollatzResearch.WordTrace tailWord_245015 prefixEnd_245015 55915761138428493949201 := by
  unfold tailWord_245015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936431207359975075640499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5957620804906650050426999 8936431207359975075640499)
  ·
    refine ⟨13404646811039962613460749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936431207359975075640499 13404646811039962613460749)
    ·
      refine ⟨5026742554139985980047781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13404646811039962613460749 5026742554139985980047781)
      ·
        refine ⟨942514228901247371258959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5026742554139985980047781 942514228901247371258959)
        ·
          refine ⟨1413771343351871056888439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942514228901247371258959 1413771343351871056888439)
          ·
            refine ⟨2120657015027806585332659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413771343351871056888439 2120657015027806585332659)
            ·
              refine ⟨3180985522541709877998989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120657015027806585332659 3180985522541709877998989)
              ·
                refine ⟨1192869570953141204249621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3180985522541709877998989 1192869570953141204249621)
                ·
                  refine ⟨55915761138428493949201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1192869570953141204249621 55915761138428493949201)
                  ·
                    rfl

theorem cell21_245015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_245015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245015 prefixEnd_245015 := by exact prefixLift 245015
  have htrace : WordTrace (prefixWord ++ tailWord_245015) baseStart_245015 baseEnd_245015 := by
    simpa [prefixWord, tailWord_245015, baseEnd_245015] using wordTrace_append hprefix tailTrace_245015
  have hstable : (prefixWord ++ tailWord_245015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245015).length < 2 ^ (prefixWord ++ tailWord_245015).sum := by decide
  have hdescent : baseEnd_245015 < baseStart_245015 := by decide
  rcases family_descends (prefixWord ++ tailWord_245015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245018 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_245018 : Nat := 118140960795 + 245018 * 2 ^ 59
def prefixEnd_245018 : Nat := 4983230072969 + 3 ^ 40 * 245018 * 2
def baseEnd_245018 : Nat := 55916445779301155399195

theorem tailTrace_245018 : CollatzResearch.WordTrace tailWord_245018 prefixEnd_245018 55916445779301155399195 := by
  unfold tailWord_245018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234135156587276646999927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5957693750899404391999805 2234135156587276646999927)
  ·
    refine ⟨3351202734880914970499891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234135156587276646999927 3351202734880914970499891)
    ·
      refine ⟨5026804102321372455749837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3351202734880914970499891 5026804102321372455749837)
      ·
        refine ⟨1885051538370514670906189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5026804102321372455749837 1885051538370514670906189)
        ·
          refine ⟨706894326888943001589821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1885051538370514670906189 706894326888943001589821)
          ·
            refine ⟨265085372583353625596183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706894326888943001589821 265085372583353625596183)
            ·
              refine ⟨397628058875030438394275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265085372583353625596183 397628058875030438394275)
              ·
                refine ⟨596442088312545657591413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397628058875030438394275 596442088312545657591413)
                ·
                  refine ⟨55916445779301155399195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 596442088312545657591413 55916445779301155399195)
                  ·
                    rfl

theorem cell21_245018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_245018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245018 prefixEnd_245018 := by exact prefixLift 245018
  have htrace : WordTrace (prefixWord ++ tailWord_245018) baseStart_245018 baseEnd_245018 := by
    simpa [prefixWord, tailWord_245018, baseEnd_245018] using wordTrace_append hprefix tailTrace_245018
  have hstable : (prefixWord ++ tailWord_245018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245018).length < 2 ^ (prefixWord ++ tailWord_245018).sum := by decide
  have hdescent : baseEnd_245018 < baseStart_245018 := by decide
  rcases family_descends (prefixWord ++ tailWord_245018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245105 : List Nat := [1, 2, 2, 2, 1, 2, 2, 9]
def baseStart_245105 : Nat := 118140960795 + 245105 * 2 ^ 59
def prefixEnd_245105 : Nat := 4983230072969 + 3 ^ 40 * 245105 * 2
def baseEnd_245105 : Nat := 18645433454869445816339

theorem tailTrace_245105 : CollatzResearch.WordTrace tailWord_245105 prefixEnd_245105 18645433454869445816339 := by
  unfold tailWord_245105
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939713777033920446416769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5959809184689280297611179 8939713777033920446416769)
  ·
    refine ⟨6704785332775440334812577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8939713777033920446416769 6704785332775440334812577)
    ·
      refine ⟨5028588999581580251109433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6704785332775440334812577 5028588999581580251109433)
      ·
        refine ⟨3771441749686185188332075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5028588999581580251109433 3771441749686185188332075)
        ·
          refine ⟨5657162624529277782498113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771441749686185188332075 5657162624529277782498113)
          ·
            refine ⟨4242871968396958336873585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657162624529277782498113 4242871968396958336873585)
            ·
              refine ⟨3182153976297718752655189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242871968396958336873585 3182153976297718752655189)
              ·
                refine ⟨18645433454869445816339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3182153976297718752655189 18645433454869445816339)
                ·
                  rfl

theorem cell21_245105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_245105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245105 prefixEnd_245105 := by exact prefixLift 245105
  have htrace : WordTrace (prefixWord ++ tailWord_245105) baseStart_245105 baseEnd_245105 := by
    simpa [prefixWord, tailWord_245105, baseEnd_245105] using wordTrace_append hprefix tailTrace_245105
  have hstable : (prefixWord ++ tailWord_245105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245105).length < 2 ^ (prefixWord ++ tailWord_245105).sum := by decide
  have hdescent : baseEnd_245105 < baseStart_245105 := by decide
  rcases family_descends (prefixWord ++ tailWord_245105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245305 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_245305 : Nat := 118140960795 + 245305 * 2 ^ 59
def prefixEnd_245305 : Nat := 4983230072969 + 3 ^ 40 * 245305 * 2
def baseEnd_245305 : Nat := 55981943089452434115275

theorem tailTrace_245305 : CollatzResearch.WordTrace tailWord_245305 prefixEnd_245305 55981943089452434115275 := by
  unfold tailWord_245305
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947008376309354603697369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5964672250872903069131579 8947008376309354603697369)
  ·
    refine ⟨6710256282232015952773027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8947008376309354603697369 6710256282232015952773027)
    ·
      refine ⟨10065384423348023929159541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710256282232015952773027 10065384423348023929159541)
      ·
        refine ⟨943629789688877243358707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10065384423348023929159541 943629789688877243358707)
        ·
          refine ⟨1415444684533315865038061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943629789688877243358707 1415444684533315865038061)
          ·
            refine ⟨530791756699993449389273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1415444684533315865038061 530791756699993449389273)
            ·
              refine ⟨398093817524995087041955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530791756699993449389273 398093817524995087041955)
              ·
                refine ⟨597140726287492630562933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398093817524995087041955 597140726287492630562933)
                ·
                  refine ⟨55981943089452434115275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 597140726287492630562933 55981943089452434115275)
                  ·
                    rfl

theorem cell21_245305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_245305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245305 prefixEnd_245305 := by exact prefixLift 245305
  have htrace : WordTrace (prefixWord ++ tailWord_245305) baseStart_245305 baseEnd_245305 := by
    simpa [prefixWord, tailWord_245305, baseEnd_245305] using wordTrace_append hprefix tailTrace_245305
  have hstable : (prefixWord ++ tailWord_245305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245305).length < 2 ^ (prefixWord ++ tailWord_245305).sum := by decide
  have hdescent : baseEnd_245305 < baseStart_245305 := by decide
  rcases family_descends (prefixWord ++ tailWord_245305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245325 : List Nat := [1, 6, 1, 1, 4, 1, 2, 5]
def baseStart_245325 : Nat := 118140960795 + 245325 * 2 ^ 59
def prefixEnd_245325 : Nat := 4983230072969 + 3 ^ 40 * 245325 * 2
def baseEnd_245325 : Nat := 18662169120645614593967

theorem tailTrace_245325 : CollatzResearch.WordTrace tailWord_245325 prefixEnd_245325 18662169120645614593967 := by
  unfold tailWord_245325
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947737836236898019425429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5965158557491265346283619 8947737836236898019425429)
  ·
    refine ⟨419425211073604594660567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8947737836236898019425429 419425211073604594660567)
    ·
      refine ⟨629137816610406891990851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419425211073604594660567 629137816610406891990851)
      ·
        refine ⟨943706724915610337986277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629137816610406891990851 943706724915610337986277)
        ·
          refine ⟨176945010921676938372427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 943706724915610337986277 176945010921676938372427)
          ·
            refine ⟨265417516382515407558641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176945010921676938372427 265417516382515407558641)
            ·
              refine ⟨199063137286886555668981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265417516382515407558641 199063137286886555668981)
              ·
                refine ⟨18662169120645614593967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199063137286886555668981 18662169120645614593967)
                ·
                  rfl

theorem cell21_245325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 5].length) (baseStart_245325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245325 prefixEnd_245325 := by exact prefixLift 245325
  have htrace : WordTrace (prefixWord ++ tailWord_245325) baseStart_245325 baseEnd_245325 := by
    simpa [prefixWord, tailWord_245325, baseEnd_245325] using wordTrace_append hprefix tailTrace_245325
  have hstable : (prefixWord ++ tailWord_245325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245325).length < 2 ^ (prefixWord ++ tailWord_245325).sum := by decide
  have hdescent : baseEnd_245325 < baseStart_245325 := by decide
  rcases family_descends (prefixWord ++ tailWord_245325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245409 : List Nat := [1, 2, 3, 3, 2, 10]
def baseStart_245409 : Nat := 118140960795 + 245409 * 2 ^ 59
def prefixEnd_245409 : Nat := 4983230072969 + 3 ^ 40 * 245409 * 2
def baseEnd_245409 : Nat := 2074284344680420903027

theorem tailTrace_245409 : CollatzResearch.WordTrace tailWord_245409 prefixEnd_245409 2074284344680420903027 := by
  unfold tailWord_245409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950801567932580365483281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5967201045288386910322187 8950801567932580365483281)
  ·
    refine ⟨6713101175949435274112461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8950801567932580365483281 6713101175949435274112461)
    ·
      refine ⟨2517412940981038227792173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6713101175949435274112461 2517412940981038227792173)
      ·
        refine ⟨944029852867889335422065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2517412940981038227792173 944029852867889335422065)
        ·
          refine ⟨708022389650917001566549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944029852867889335422065 708022389650917001566549)
          ·
            refine ⟨2074284344680420903027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 708022389650917001566549 2074284344680420903027)
            ·
              rfl

theorem cell21_245409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 10].length) (baseStart_245409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245409 prefixEnd_245409 := by exact prefixLift 245409
  have htrace : WordTrace (prefixWord ++ tailWord_245409) baseStart_245409 baseEnd_245409 := by
    simpa [prefixWord, tailWord_245409, baseEnd_245409] using wordTrace_append hprefix tailTrace_245409
  have hstable : (prefixWord ++ tailWord_245409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245409).length < 2 ^ (prefixWord ++ tailWord_245409).sum := by decide
  have hdescent : baseEnd_245409 < baseStart_245409 := by decide
  rcases family_descends (prefixWord ++ tailWord_245409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245412 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_245412 : Nat := 118140960795 + 245412 * 2 ^ 59
def prefixEnd_245412 : Nat := 4983230072969 + 3 ^ 40 * 245412 * 2
def baseEnd_245412 : Nat := 56006361947244025831723

theorem tailTrace_245412 : CollatzResearch.WordTrace tailWord_245412 prefixEnd_245412 56006361947244025831723 := by
  unfold tailWord_245412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475455493460855938921245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5967273991281141251894993 4475455493460855938921245)
  ·
    refine ⟨1678295810047820977095467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4475455493460855938921245 1678295810047820977095467)
    ·
      refine ⟨2517443715071731465643201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678295810047820977095467 2517443715071731465643201)
      ·
        refine ⟨1888082786303798599232401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2517443715071731465643201 1888082786303798599232401)
        ·
          refine ⟨1416062089727848949424301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888082786303798599232401 1416062089727848949424301)
          ·
            refine ⟨531023283647943356034113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1416062089727848949424301 531023283647943356034113)
            ·
              refine ⟨398267462735957517025585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531023283647943356034113 398267462735957517025585)
              ·
                refine ⟨298700597051968137769189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398267462735957517025585 298700597051968137769189)
                ·
                  refine ⟨56006361947244025831723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298700597051968137769189 56006361947244025831723)
                  ·
                    rfl

theorem cell21_245412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_245412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245412 prefixEnd_245412 := by exact prefixLift 245412
  have htrace : WordTrace (prefixWord ++ tailWord_245412) baseStart_245412 baseEnd_245412 := by
    simpa [prefixWord, tailWord_245412, baseEnd_245412] using wordTrace_append hprefix tailTrace_245412
  have hstable : (prefixWord ++ tailWord_245412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245412).length < 2 ^ (prefixWord ++ tailWord_245412).sum := by decide
  have hdescent : baseEnd_245412 < baseStart_245412 := by decide
  rcases family_descends (prefixWord ++ tailWord_245412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245440 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_245440 : Nat := 118140960795 + 245440 * 2 ^ 59
def prefixEnd_245440 : Nat := 4983230072969 + 3 ^ 40 * 245440 * 2
def baseEnd_245440 : Nat := 56012751928722199364999

theorem tailTrace_245440 : CollatzResearch.WordTrace tailWord_245440 prefixEnd_245440 56012751928722199364999 := by
  unfold tailWord_245440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475966115410136329930887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5967954820546848439907849 4475966115410136329930887)
  ·
    refine ⟨6713949173115204494896331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4475966115410136329930887 6713949173115204494896331)
    ·
      refine ⟨10070923759672806742344497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6713949173115204494896331 10070923759672806742344497)
      ·
        refine ⟨7553192819754605056758373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10070923759672806742344497 7553192819754605056758373)
        ·
          refine ⟨1416223653703988448142195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7553192819754605056758373 1416223653703988448142195)
          ·
            refine ⟨2124335480555982672213293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416223653703988448142195 2124335480555982672213293)
            ·
              refine ⟨796625805208493502079985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124335480555982672213293 796625805208493502079985)
              ·
                refine ⟨597469353906370126559989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796625805208493502079985 597469353906370126559989)
                ·
                  refine ⟨56012751928722199364999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 597469353906370126559989 56012751928722199364999)
                  ·
                    rfl

theorem cell21_245440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_245440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245440 prefixEnd_245440 := by exact prefixLift 245440
  have htrace : WordTrace (prefixWord ++ tailWord_245440) baseStart_245440 baseEnd_245440 := by
    simpa [prefixWord, tailWord_245440, baseEnd_245440] using wordTrace_append hprefix tailTrace_245440
  have hstable : (prefixWord ++ tailWord_245440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245440).length < 2 ^ (prefixWord ++ tailWord_245440).sum := by decide
  have hdescent : baseEnd_245440 < baseStart_245440 := by decide
  rcases family_descends (prefixWord ++ tailWord_245440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245457 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 3]
def baseStart_245457 : Nat := 118140960795 + 245457 * 2 ^ 59
def prefixEnd_245457 : Nat := 4983230072969 + 3 ^ 40 * 245457 * 2
def baseEnd_245457 : Nat := 56016631560333947581631

theorem tailTrace_245457 : CollatzResearch.WordTrace tailWord_245457 prefixEnd_245457 56016631560333947581631 := by
  unfold tailWord_245457
  simp only [CollatzResearch.WordTrace]
  refine ⟨8952552271758684563230625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5968368181172456375487083 8952552271758684563230625)
  ·
    refine ⟨6714414203819013422422969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8952552271758684563230625 6714414203819013422422969)
    ·
      refine ⟨5035810652864260066817227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6714414203819013422422969 5035810652864260066817227)
      ·
        refine ⟨7553715979296390100225841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035810652864260066817227 7553715979296390100225841)
        ·
          refine ⟨5665286984472292575169381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553715979296390100225841 5665286984472292575169381)
          ·
            refine ⟨1062241309588554857844259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5665286984472292575169381 1062241309588554857844259)
            ·
              refine ⟨1593361964382832286766389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062241309588554857844259 1593361964382832286766389)
              ·
                refine ⟨149377684160890526884349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1593361964382832286766389 149377684160890526884349)
                ·
                  refine ⟨56016631560333947581631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149377684160890526884349 56016631560333947581631)
                  ·
                    rfl

theorem cell21_245457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_245457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245457 prefixEnd_245457 := by exact prefixLift 245457
  have htrace : WordTrace (prefixWord ++ tailWord_245457) baseStart_245457 baseEnd_245457 := by
    simpa [prefixWord, tailWord_245457, baseEnd_245457] using wordTrace_append hprefix tailTrace_245457
  have hstable : (prefixWord ++ tailWord_245457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245457).length < 2 ^ (prefixWord ++ tailWord_245457).sum := by decide
  have hdescent : baseEnd_245457 < baseStart_245457 := by decide
  rcases family_descends (prefixWord ++ tailWord_245457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245499 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_245499 : Nat := 118140960795 + 245499 * 2 ^ 59
def prefixEnd_245499 : Nat := 4983230072969 + 3 ^ 40 * 245499 * 2
def baseEnd_245499 : Nat := 56026216532551207881545

theorem tailTrace_245499 : CollatzResearch.WordTrace tailWord_245499 prefixEnd_245499 56026216532551207881545 := by
  unfold tailWord_245499
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954084137606525736259551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5969389425071017157506367 8954084137606525736259551)
  ·
    refine ⟨13431126206409788604389327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954084137606525736259551 13431126206409788604389327)
    ·
      refine ⟨20146689309614682906583991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431126206409788604389327 20146689309614682906583991)
      ·
        refine ⟨30220033964422024359875987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20146689309614682906583991 30220033964422024359875987)
        ·
          refine ⟨45330050946633036539813981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30220033964422024359875987 45330050946633036539813981)
          ·
            refine ⟨16998769104987388702430243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45330050946633036539813981 16998769104987388702430243)
            ·
              refine ⟨25498153657481083053645365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16998769104987388702430243 25498153657481083053645365)
              ·
                refine ⟨2390451905388851536279253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25498153657481083053645365 2390451905388851536279253)
                ·
                  refine ⟨56026216532551207881545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2390451905388851536279253 56026216532551207881545)
                  ·
                    rfl

theorem cell21_245499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_245499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245499 prefixEnd_245499 := by exact prefixLift 245499
  have htrace : WordTrace (prefixWord ++ tailWord_245499) baseStart_245499 baseEnd_245499 := by
    simpa [prefixWord, tailWord_245499, baseEnd_245499] using wordTrace_append hprefix tailTrace_245499
  have hstable : (prefixWord ++ tailWord_245499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245499).length < 2 ^ (prefixWord ++ tailWord_245499).sum := by decide
  have hdescent : baseEnd_245499 < baseStart_245499 := by decide
  rcases family_descends (prefixWord ++ tailWord_245499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245581 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_245581 : Nat := 118140960795 + 245581 * 2 ^ 59
def prefixEnd_245581 : Nat := 4983230072969 + 3 ^ 40 * 245581 * 2
def baseEnd_245581 : Nat := 56044930049737287514711

theorem tailTrace_245581 : CollatzResearch.WordTrace tailWord_245581 prefixEnd_245581 56044930049737287514711 := by
  unfold tailWord_245581
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957074923309453740744597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5971383282206302493829731 8957074923309453740744597)
  ·
    refine ⟨419862887030130644097403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8957074923309453740744597 419862887030130644097403)
    ·
      refine ⟨629794330545195966146105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419862887030130644097403 629794330545195966146105)
      ·
        refine ⟨472345747908896974609579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629794330545195966146105 472345747908896974609579)
        ·
          refine ⟨708518621863345461914369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472345747908896974609579 708518621863345461914369)
          ·
            refine ⟨531388966397509096435777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708518621863345461914369 531388966397509096435777)
            ·
              refine ⟨398541724798131822326833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531388966397509096435777 398541724798131822326833)
              ·
                refine ⟨298906293598598866745125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398541724798131822326833 298906293598598866745125)
                ·
                  refine ⟨56044930049737287514711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298906293598598866745125 56044930049737287514711)
                  ·
                    rfl

theorem cell21_245581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_245581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245581 prefixEnd_245581 := by exact prefixLift 245581
  have htrace : WordTrace (prefixWord ++ tailWord_245581) baseStart_245581 baseEnd_245581 := by
    simpa [prefixWord, tailWord_245581, baseEnd_245581] using wordTrace_append hprefix tailTrace_245581
  have hstable : (prefixWord ++ tailWord_245581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245581).length < 2 ^ (prefixWord ++ tailWord_245581).sum := by decide
  have hdescent : baseEnd_245581 < baseStart_245581 := by decide
  rcases family_descends (prefixWord ++ tailWord_245581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245668 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_245668 : Nat := 118140960795 + 245668 * 2 ^ 59
def prefixEnd_245668 : Nat := 4983230072969 + 3 ^ 40 * 245668 * 2
def baseEnd_245668 : Nat := 56064784635044469564533

theorem tailTrace_245668 : CollatzResearch.WordTrace tailWord_245668 prefixEnd_245668 56064784635044469564533 := by
  unfold tailWord_245668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480124036997133799580829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5973498715996178399441105 4480124036997133799580829)
  ·
    refine ⟨1680046513873925174842811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4480124036997133799580829 1680046513873925174842811)
    ·
      refine ⟨2520069770810887762264217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680046513873925174842811 2520069770810887762264217)
      ·
        refine ⟨1890052328108165821698163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520069770810887762264217 1890052328108165821698163)
        ·
          refine ⟨2835078492162248732547245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890052328108165821698163 2835078492162248732547245)
          ·
            refine ⟨1063154434560843274705217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2835078492162248732547245 1063154434560843274705217)
            ·
              refine ⟨797365825920632456028913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063154434560843274705217 797365825920632456028913)
              ·
                refine ⟨598024369440474342021685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797365825920632456028913 598024369440474342021685)
                ·
                  refine ⟨56064784635044469564533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598024369440474342021685 56064784635044469564533)
                  ·
                    rfl

theorem cell21_245668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_245668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245668 prefixEnd_245668 := by exact prefixLift 245668
  have htrace : WordTrace (prefixWord ++ tailWord_245668) baseStart_245668 baseEnd_245668 := by
    simpa [prefixWord, tailWord_245668, baseEnd_245668] using wordTrace_append hprefix tailTrace_245668
  have hstable : (prefixWord ++ tailWord_245668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245668).length < 2 ^ (prefixWord ++ tailWord_245668).sum := by decide
  have hdescent : baseEnd_245668 < baseStart_245668 := by decide
  rcases family_descends (prefixWord ++ tailWord_245668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245671 : List Nat := [1, 1, 6, 1, 2, 3, 2, 5]
def baseStart_245671 : Nat := 118140960795 + 245671 * 2 ^ 59
def prefixEnd_245671 : Nat := 4983230072969 + 3 ^ 40 * 245671 * 2
def baseEnd_245671 : Nat := 18688489758639043671509

theorem tailTrace_245671 : CollatzResearch.WordTrace tailWord_245671 prefixEnd_245671 18688489758639043671509 := by
  unfold tailWord_245671
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960357492983399111520867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5973571661988932741013911 8960357492983399111520867)
  ·
    refine ⟨13440536239475098667281301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8960357492983399111520867 13440536239475098667281301)
    ·
      refine ⟨630025136225395250028811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13440536239475098667281301 630025136225395250028811)
      ·
        refine ⟨945037704338092875043217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630025136225395250028811 945037704338092875043217)
        ·
          refine ⟨708778278253569656282413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945037704338092875043217 708778278253569656282413)
          ·
            refine ⟨265791854345088621105905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708778278253569656282413 265791854345088621105905)
            ·
              refine ⟨199343890758816465829429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265791854345088621105905 199343890758816465829429)
              ·
                refine ⟨18688489758639043671509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199343890758816465829429 18688489758639043671509)
                ·
                  rfl

theorem cell21_245671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 5].length) (baseStart_245671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245671 prefixEnd_245671 := by exact prefixLift 245671
  have htrace : WordTrace (prefixWord ++ tailWord_245671) baseStart_245671 baseEnd_245671 := by
    simpa [prefixWord, tailWord_245671, baseEnd_245671] using wordTrace_append hprefix tailTrace_245671
  have hstable : (prefixWord ++ tailWord_245671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245671).length < 2 ^ (prefixWord ++ tailWord_245671).sum := by decide
  have hdescent : baseEnd_245671 < baseStart_245671 := by decide
  rcases family_descends (prefixWord ++ tailWord_245671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245761 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 3]
def baseStart_245761 : Nat := 118140960795 + 245761 * 2 ^ 59
def prefixEnd_245761 : Nat := 4983230072969 + 3 ^ 40 * 245761 * 2
def baseEnd_245761 : Nat := 56086008502096974514343

theorem tailTrace_245761 : CollatzResearch.WordTrace tailWord_245761 prefixEnd_245761 56086008502096974514343 := by
  unfold tailWord_245761
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963640062657344482297137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5975760041771562988198091 8963640062657344482297137)
  ·
    refine ⟨6722730046993008361722853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8963640062657344482297137 6722730046993008361722853)
    ·
      refine ⟨1260511883811189067823035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6722730046993008361722853 1260511883811189067823035)
      ·
        refine ⟨1890767825716783601734553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260511883811189067823035 1890767825716783601734553)
        ·
          refine ⟨1418075869287587701300915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890767825716783601734553 1418075869287587701300915)
          ·
            refine ⟨2127113803931381551951373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418075869287587701300915 2127113803931381551951373)
            ·
              refine ⟨797667676474268081981765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2127113803931381551951373 797667676474268081981765)
              ·
                refine ⟨149562689338925265371581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797667676474268081981765 149562689338925265371581)
                ·
                  refine ⟨56086008502096974514343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149562689338925265371581 56086008502096974514343)
                  ·
                    rfl

theorem cell21_245761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_245761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245761 prefixEnd_245761 := by exact prefixLift 245761
  have htrace : WordTrace (prefixWord ++ tailWord_245761) baseStart_245761 baseEnd_245761 := by
    simpa [prefixWord, tailWord_245761, baseEnd_245761] using wordTrace_append hprefix tailTrace_245761
  have hstable : (prefixWord ++ tailWord_245761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245761).length < 2 ^ (prefixWord ++ tailWord_245761).sum := by decide
  have hdescent : baseEnd_245761 < baseStart_245761 := by decide
  rcases family_descends (prefixWord ++ tailWord_245761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245764 : List Nat := [2, 3, 2, 4, 2, 1, 1, 6]
def baseStart_245764 : Nat := 118140960795 + 245764 * 2 ^ 59
def prefixEnd_245764 : Nat := 4983230072969 + 3 ^ 40 * 245764 * 2
def baseEnd_245764 : Nat := 18695564380989878654779

theorem tailTrace_245764 : CollatzResearch.WordTrace tailWord_245764 prefixEnd_245764 18695564380989878654779 := by
  unfold tailWord_245764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481874740823237997328173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5975832987764317329770897 4481874740823237997328173)
  ·
    refine ⟨1680703027808714248998065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4481874740823237997328173 1680703027808714248998065)
    ·
      refine ⟨1260527270856535686748549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1680703027808714248998065 1260527270856535686748549)
      ·
        refine ⟨236348863285600441265353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1260527270856535686748549 236348863285600441265353)
        ·
          refine ⟨177261647464200330949015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236348863285600441265353 177261647464200330949015)
          ·
            refine ⟨265892471196300496423523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177261647464200330949015 265892471196300496423523)
            ·
              refine ⟨398838706794450744635285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265892471196300496423523 398838706794450744635285)
              ·
                refine ⟨18695564380989878654779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 398838706794450744635285 18695564380989878654779)
                ·
                  rfl

theorem cell21_245764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_245764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245764 prefixEnd_245764 := by exact prefixLift 245764
  have htrace : WordTrace (prefixWord ++ tailWord_245764) baseStart_245764 baseEnd_245764 := by
    simpa [prefixWord, tailWord_245764, baseEnd_245764] using wordTrace_append hprefix tailTrace_245764
  have hstable : (prefixWord ++ tailWord_245764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245764).length < 2 ^ (prefixWord ++ tailWord_245764).sum := by decide
  have hdescent : baseEnd_245764 < baseStart_245764 := by decide
  rcases family_descends (prefixWord ++ tailWord_245764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245820 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_245820 : Nat := 118140960795 + 245820 * 2 ^ 59
def prefixEnd_245820 : Nat := 4983230072969 + 3 ^ 40 * 245820 * 2
def baseEnd_245820 : Nat := 56099473105925983030889

theorem tailTrace_245820 : CollatzResearch.WordTrace tailWord_245820 prefixEnd_245820 56099473105925983030889 := by
  unfold tailWord_245820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482895984721798779347457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5977194646295731705796609 4482895984721798779347457)
  ·
    refine ⟨3362171988541349084510593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4482895984721798779347457 3362171988541349084510593)
    ·
      refine ⟨2521628991406011813382945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3362171988541349084510593 2521628991406011813382945)
      ·
        refine ⟨1891221743554508860037209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521628991406011813382945 1891221743554508860037209)
        ·
          refine ⟨1418416307665881645027907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1891221743554508860037209 1418416307665881645027907)
          ·
            refine ⟨2127624461498822467541861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418416307665881645027907 2127624461498822467541861)
            ·
              refine ⟨398929586531029212664099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2127624461498822467541861 398929586531029212664099)
              ·
                refine ⟨598394379796543818996149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398929586531029212664099 598394379796543818996149)
                ·
                  refine ⟨56099473105925983030889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598394379796543818996149 56099473105925983030889)
                  ·
                    rfl

theorem cell21_245820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_245820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245820 prefixEnd_245820 := by exact prefixLift 245820
  have htrace : WordTrace (prefixWord ++ tailWord_245820) baseStart_245820 baseEnd_245820 := by
    simpa [prefixWord, tailWord_245820, baseEnd_245820] using wordTrace_append hprefix tailTrace_245820
  have hstable : (prefixWord ++ tailWord_245820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245820).length < 2 ^ (prefixWord ++ tailWord_245820).sum := by decide
  have hdescent : baseEnd_245820 < baseStart_245820 := by decide
  rcases family_descends (prefixWord ++ tailWord_245820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245924 : List Nat := [2, 3, 1, 2, 13]
def baseStart_245924 : Nat := 118140960795 + 245924 * 2 ^ 59
def prefixEnd_245924 : Nat := 4983230072969 + 3 ^ 40 * 245924 * 2
def baseEnd_245924 : Nat := 692879102751171769103

theorem tailTrace_245924 : CollatzResearch.WordTrace tailWord_245924 prefixEnd_245924 692879102751171769103 := by
  unfold tailWord_245924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484792580533411660240413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5979723440711215546987217 4484792580533411660240413)
  ·
    refine ⟨1681797217700029372590155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4484792580533411660240413 1681797217700029372590155)
    ·
      refine ⟨2522695826550044058885233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681797217700029372590155 2522695826550044058885233)
      ·
        refine ⟨1892021869912533044163925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2522695826550044058885233 1892021869912533044163925)
        ·
          refine ⟨692879102751171769103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1892021869912533044163925 692879102751171769103)
          ·
            rfl

theorem cell21_245924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 13].length) (baseStart_245924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245924 prefixEnd_245924 := by exact prefixLift 245924
  have htrace : WordTrace (prefixWord ++ tailWord_245924) baseStart_245924 baseEnd_245924 := by
    simpa [prefixWord, tailWord_245924, baseEnd_245924] using wordTrace_append hprefix tailTrace_245924
  have hstable : (prefixWord ++ tailWord_245924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245924).length < 2 ^ (prefixWord ++ tailWord_245924).sum := by decide
  have hdescent : baseEnd_245924 < baseStart_245924 := by decide
  rcases family_descends (prefixWord ++ tailWord_245924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245989 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 3]
def baseStart_245989 : Nat := 118140960795 + 245989 * 2 ^ 59
def prefixEnd_245989 : Nat := 4983230072969 + 3 ^ 40 * 245989 * 2
def baseEnd_245989 : Nat := 56138041208419244713877

theorem tailTrace_245989 : CollatzResearch.WordTrace tailWord_245989 prefixEnd_245989 56138041208419244713877 := by
  unfold tailWord_245989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971955905831339421597021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5981303937220892947731347 8971955905831339421597021)
  ·
    refine ⟨3364483464686752283098883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8971955905831339421597021 3364483464686752283098883)
    ·
      refine ⟨5046725197030128424648325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364483464686752283098883 5046725197030128424648325)
      ·
        refine ⟨946260974443149079621561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5046725197030128424648325 946260974443149079621561)
        ·
          refine ⟨709695730832361809716171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946260974443149079621561 709695730832361809716171)
          ·
            refine ⟨1064543596248542714574257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709695730832361809716171 1064543596248542714574257)
            ·
              refine ⟨798407697186407035930693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064543596248542714574257 798407697186407035930693)
              ·
                refine ⟨149701443222451319237005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 798407697186407035930693 149701443222451319237005)
                ·
                  refine ⟨56138041208419244713877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149701443222451319237005 56138041208419244713877)
                  ·
                    rfl

theorem cell21_245989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_245989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_245989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_245989 prefixEnd_245989 := by exact prefixLift 245989
  have htrace : WordTrace (prefixWord ++ tailWord_245989) baseStart_245989 baseEnd_245989 := by
    simpa [prefixWord, tailWord_245989, baseEnd_245989] using wordTrace_append hprefix tailTrace_245989
  have hstable : (prefixWord ++ tailWord_245989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245989).length < 2 ^ (prefixWord ++ tailWord_245989).sum := by decide
  have hdescent : baseEnd_245989 < baseStart_245989 := by decide
  rcases family_descends (prefixWord ++ tailWord_245989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246003 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 4]
def baseStart_246003 : Nat := 118140960795 + 246003 * 2 ^ 59
def prefixEnd_246003 : Nat := 4983230072969 + 3 ^ 40 * 246003 * 2
def baseEnd_246003 : Nat := 56141236199158331480515

theorem tailTrace_246003 : CollatzResearch.WordTrace tailWord_246003 prefixEnd_246003 56141236199158331480515 := by
  unfold tailWord_246003
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972466527780619812606663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5981644351853746541737775 8972466527780619812606663)
  ·
    refine ⟨13458699791670929718909995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8972466527780619812606663 13458699791670929718909995)
    ·
      refine ⟨20188049687506394578364993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13458699791670929718909995 20188049687506394578364993)
      ·
        refine ⟨15141037265629795933773745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20188049687506394578364993 15141037265629795933773745)
        ·
          refine ⟨11355777949222346950330309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141037265629795933773745 11355777949222346950330309)
          ·
            refine ⟨2129208365479190053186933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11355777949222346950330309 2129208365479190053186933)
            ·
              refine ⟨199613284263674067486275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2129208365479190053186933 199613284263674067486275)
              ·
                refine ⟨299419926395511101229413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199613284263674067486275 299419926395511101229413)
                ·
                  refine ⟨56141236199158331480515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299419926395511101229413 56141236199158331480515)
                  ·
                    rfl

theorem cell21_246003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4].length) (baseStart_246003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246003 prefixEnd_246003 := by exact prefixLift 246003
  have htrace : WordTrace (prefixWord ++ tailWord_246003) baseStart_246003 baseEnd_246003 := by
    simpa [prefixWord, tailWord_246003, baseEnd_246003] using wordTrace_append hprefix tailTrace_246003
  have hstable : (prefixWord ++ tailWord_246003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246003).length < 2 ^ (prefixWord ++ tailWord_246003).sum := by decide
  have hdescent : baseEnd_246003 < baseStart_246003 := by decide
  rcases family_descends (prefixWord ++ tailWord_246003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246023 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 3]
def baseStart_246023 : Nat := 118140960795 + 246023 * 2 ^ 59
def prefixEnd_246023 : Nat := 4983230072969 + 3 ^ 40 * 246023 * 2
def baseEnd_246023 : Nat := 56145800471642741147141

theorem tailTrace_246023 : CollatzResearch.WordTrace tailWord_246023 prefixEnd_246023 56145800471642741147141 := by
  unfold tailWord_246023
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973195987708163228334723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5982130658472108818889815 8973195987708163228334723)
  ·
    refine ⟨13459793981562244842502085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8973195987708163228334723 13459793981562244842502085)
    ·
      refine ⟨2523711371542920907969141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13459793981562244842502085 2523711371542920907969141)
      ·
        refine ⟨236597941082148835122107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2523711371542920907969141 236597941082148835122107)
        ·
          refine ⟨354896911623223252683161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236597941082148835122107 354896911623223252683161)
          ·
            refine ⟨266172683717417439512371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354896911623223252683161 266172683717417439512371)
            ·
              refine ⟨399259025576126159268557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266172683717417439512371 399259025576126159268557)
              ·
                refine ⟨149722134591047309725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399259025576126159268557 149722134591047309725709)
                ·
                  refine ⟨56145800471642741147141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149722134591047309725709 56145800471642741147141)
                  ·
                    rfl

theorem cell21_246023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 3].length) (baseStart_246023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246023 prefixEnd_246023 := by exact prefixLift 246023
  have htrace : WordTrace (prefixWord ++ tailWord_246023) baseStart_246023 baseEnd_246023 := by
    simpa [prefixWord, tailWord_246023, baseEnd_246023] using wordTrace_append hprefix tailTrace_246023
  have hstable : (prefixWord ++ tailWord_246023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246023).length < 2 ^ (prefixWord ++ tailWord_246023).sum := by decide
  have hdescent : baseEnd_246023 < baseStart_246023 := by decide
  rcases family_descends (prefixWord ++ tailWord_246023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246048 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_246048 : Nat := 118140960795 + 246048 * 2 ^ 59
def prefixEnd_246048 : Nat := 4983230072969 + 3 ^ 40 * 246048 * 2
def baseEnd_246048 : Nat := 56151505812248253230423

theorem tailTrace_246048 : CollatzResearch.WordTrace tailWord_246048 prefixEnd_246048 56151505812248253230423 := by
  unfold tailWord_246048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487053906308796248997399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5982738541745061665329865 4487053906308796248997399)
  ·
    refine ⟨6730580859463194373496099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4487053906308796248997399 6730580859463194373496099)
    ·
      refine ⟨10095871289194791560244149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6730580859463194373496099 10095871289194791560244149)
      ·
        refine ⟨946487933362011708772889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10095871289194791560244149 946487933362011708772889)
        ·
          refine ⟨709865950021508781579667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946487933362011708772889 709865950021508781579667)
          ·
            refine ⟨1064798925032263172369501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709865950021508781579667 1064798925032263172369501)
            ·
              refine ⟨399299596887098689638563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1064798925032263172369501 399299596887098689638563)
              ·
                refine ⟨598949395330648034457845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399299596887098689638563 598949395330648034457845)
                ·
                  refine ⟨56151505812248253230423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 598949395330648034457845 56151505812248253230423)
                  ·
                    rfl

theorem cell21_246048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_246048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246048 prefixEnd_246048 := by exact prefixLift 246048
  have htrace : WordTrace (prefixWord ++ tailWord_246048) baseStart_246048 baseEnd_246048 := by
    simpa [prefixWord, tailWord_246048, baseEnd_246048] using wordTrace_append hprefix tailTrace_246048
  have hstable : (prefixWord ++ tailWord_246048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246048).length < 2 ^ (prefixWord ++ tailWord_246048).sum := by decide
  have hdescent : baseEnd_246048 < baseStart_246048 := by decide
  rcases family_descends (prefixWord ++ tailWord_246048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246076 : List Nat := [2, 2, 2, 2, 1, 2, 1, 9]
def baseStart_246076 : Nat := 118140960795 + 246076 * 2 ^ 59
def prefixEnd_246076 : Nat := 4983230072969 + 3 ^ 40 * 246076 * 2
def baseEnd_246076 : Nat := 18719298597908808921233

theorem tailTrace_246076 : CollatzResearch.WordTrace tailWord_246076 prefixEnd_246076 18719298597908808921233 := by
  unfold tailWord_246076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487564528258076640007041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5983419371010768853342721 4487564528258076640007041)
  ·
    refine ⟨3365673396193557480005281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4487564528258076640007041 3365673396193557480005281)
    ·
      refine ⟨2524255047145168110003961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3365673396193557480005281 2524255047145168110003961)
      ·
        refine ⟨1893191285358876082502971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2524255047145168110003961 1893191285358876082502971)
        ·
          refine ⟨2839786928038314123754457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893191285358876082502971 2839786928038314123754457)
          ·
            refine ⟨2129840196028735592815843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839786928038314123754457 2129840196028735592815843)
            ·
              refine ⟨3194760294043103389223765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129840196028735592815843 3194760294043103389223765)
              ·
                refine ⟨18719298597908808921233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3194760294043103389223765 18719298597908808921233)
                ·
                  rfl

theorem cell21_246076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_246076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246076 prefixEnd_246076 := by exact prefixLift 246076
  have htrace : WordTrace (prefixWord ++ tailWord_246076) baseStart_246076 baseEnd_246076 := by
    simpa [prefixWord, tailWord_246076, baseEnd_246076] using wordTrace_append hprefix tailTrace_246076
  have hstable : (prefixWord ++ tailWord_246076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246076).length < 2 ^ (prefixWord ++ tailWord_246076).sum := by decide
  have hdescent : baseEnd_246076 < baseStart_246076 := by decide
  rcases family_descends (prefixWord ++ tailWord_246076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246124 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_246124 : Nat := 118140960795 + 246124 * 2 ^ 59
def prefixEnd_246124 : Nat := 4983230072969 + 3 ^ 40 * 246124 * 2
def baseEnd_246124 : Nat := 56168850047689009963601

theorem tailTrace_246124 : CollatzResearch.WordTrace tailWord_246124 prefixEnd_246124 56168850047689009963601 := by
  unfold tailWord_246124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488439880171128738880713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5984586506894838318507617 4488439880171128738880713)
  ·
    refine ⟨3366329910128346554160535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4488439880171128738880713 3366329910128346554160535)
    ·
      refine ⟨5049494865192519831240803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366329910128346554160535 5049494865192519831240803)
      ·
        refine ⟨7574242297788779746861205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049494865192519831240803 7574242297788779746861205)
        ·
          refine ⟨355042607708849050634119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7574242297788779746861205 355042607708849050634119)
          ·
            refine ⟨532563911563273575951179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355042607708849050634119 532563911563273575951179)
            ·
              refine ⟨798845867344910363926769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532563911563273575951179 798845867344910363926769)
              ·
                refine ⟨599134400508682772945077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798845867344910363926769 599134400508682772945077)
                ·
                  refine ⟨56168850047689009963601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599134400508682772945077 56168850047689009963601)
                  ·
                    rfl

theorem cell21_246124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_246124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246124 prefixEnd_246124 := by exact prefixLift 246124
  have htrace : WordTrace (prefixWord ++ tailWord_246124) baseStart_246124 baseEnd_246124 := by
    simpa [prefixWord, tailWord_246124, baseEnd_246124] using wordTrace_append hprefix tailTrace_246124
  have hstable : (prefixWord ++ tailWord_246124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246124).length < 2 ^ (prefixWord ++ tailWord_246124).sum := by decide
  have hdescent : baseEnd_246124 < baseStart_246124 := by decide
  rcases family_descends (prefixWord ++ tailWord_246124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246141 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 3]
def baseStart_246141 : Nat := 118140960795 + 246141 * 2 ^ 59
def prefixEnd_246141 : Nat := 4983230072969 + 3 ^ 40 * 246141 * 2
def baseEnd_246141 : Nat := 56172729679300758180233

theorem tailTrace_246141 : CollatzResearch.WordTrace tailWord_246141 prefixEnd_246141 56172729679300758180233 := by
  unfold tailWord_246141
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977499801280669381130277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5984999867520446254086851 8977499801280669381130277)
  ·
    refine ⟨1683281212740125508961927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8977499801280669381130277 1683281212740125508961927)
    ·
      refine ⟨2524921819110188263442891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683281212740125508961927 2524921819110188263442891)
      ·
        refine ⟨3787382728665282395164337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524921819110188263442891 3787382728665282395164337)
        ·
          refine ⟨2840537046498961796373253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787382728665282395164337 2840537046498961796373253)
          ·
            refine ⟨532600696218555336819985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2840537046498961796373253 532600696218555336819985)
            ·
              refine ⟨399450522163916502614989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532600696218555336819985 399450522163916502614989)
              ·
                refine ⟨149793945811468688480621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399450522163916502614989 149793945811468688480621)
                ·
                  refine ⟨56172729679300758180233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149793945811468688480621 56172729679300758180233)
                  ·
                    rfl

theorem cell21_246141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_246141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246141 prefixEnd_246141 := by exact prefixLift 246141
  have htrace : WordTrace (prefixWord ++ tailWord_246141) baseStart_246141 baseEnd_246141 := by
    simpa [prefixWord, tailWord_246141, baseEnd_246141] using wordTrace_append hprefix tailTrace_246141
  have hstable : (prefixWord ++ tailWord_246141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246141).length < 2 ^ (prefixWord ++ tailWord_246141).sum := by decide
  have hdescent : baseEnd_246141 < baseStart_246141 := by decide
  rcases family_descends (prefixWord ++ tailWord_246141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246152 : List Nat := [2, 1, 3, 3, 1, 1, 10]
def baseStart_246152 : Nat := 118140960795 + 246152 * 2 ^ 59
def prefixEnd_246152 : Nat := 4983230072969 + 3 ^ 40 * 246152 * 2
def baseEnd_246152 : Nat := 6241693336574131499653

theorem tailTrace_246152 : CollatzResearch.WordTrace tailWord_246152 prefixEnd_246152 6241693336574131499653 := by
  unfold tailWord_246152
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488950502120409129890355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5985267336160545506520473 4488950502120409129890355)
  ·
    refine ⟨6733425753180613694835533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4488950502120409129890355 6733425753180613694835533)
    ·
      refine ⟨2525034657442730135563325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6733425753180613694835533 2525034657442730135563325)
      ·
        refine ⟨946887996541023800836247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2525034657442730135563325 946887996541023800836247)
        ·
          refine ⟨1420331994811535701254371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946887996541023800836247 1420331994811535701254371)
          ·
            refine ⟨2130497992217303551881557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420331994811535701254371 2130497992217303551881557)
            ·
              refine ⟨6241693336574131499653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2130497992217303551881557 6241693336574131499653)
              ·
                rfl

theorem cell21_246152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 10].length) (baseStart_246152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246152 prefixEnd_246152 := by exact prefixLift 246152
  have htrace : WordTrace (prefixWord ++ tailWord_246152) baseStart_246152 baseEnd_246152 := by
    simpa [prefixWord, tailWord_246152, baseEnd_246152] using wordTrace_append hprefix tailTrace_246152
  have hstable : (prefixWord ++ tailWord_246152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246152).length < 2 ^ (prefixWord ++ tailWord_246152).sum := by decide
  have hdescent : baseEnd_246152 < baseStart_246152 := by decide
  rcases family_descends (prefixWord ++ tailWord_246152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246155 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 4]
def baseStart_246155 : Nat := 118140960795 + 246155 * 2 ^ 59
def prefixEnd_246155 : Nat := 4983230072969 + 3 ^ 40 * 246155 * 2
def baseEnd_246155 : Nat := 56175924670039844946871

theorem tailTrace_246155 : CollatzResearch.WordTrace tailWord_246155 prefixEnd_246155 56175924670039844946871 := by
  unfold tailWord_246155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978010423229949772139919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5985340282153299848093279 8978010423229949772139919)
  ·
    refine ⟨13467015634844924658209879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8978010423229949772139919 13467015634844924658209879)
    ·
      refine ⟨20200523452267386987314819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13467015634844924658209879 20200523452267386987314819)
      ·
        refine ⟨30300785178401080480972229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20200523452267386987314819 30300785178401080480972229)
        ·
          refine ⟨5681397220950202590182293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30300785178401080480972229 5681397220950202590182293)
          ·
            refine ⟨266315494732040746414795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5681397220950202590182293 266315494732040746414795)
            ·
              refine ⟨399473242098061119622193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266315494732040746414795 399473242098061119622193)
              ·
                refine ⟨299604931573545839716645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399473242098061119622193 299604931573545839716645)
                ·
                  refine ⟨56175924670039844946871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299604931573545839716645 56175924670039844946871)
                  ·
                    rfl

theorem cell21_246155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_246155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246155 prefixEnd_246155 := by exact prefixLift 246155
  have htrace : WordTrace (prefixWord ++ tailWord_246155) baseStart_246155 baseEnd_246155 := by
    simpa [prefixWord, tailWord_246155, baseEnd_246155] using wordTrace_append hprefix tailTrace_246155
  have hstable : (prefixWord ++ tailWord_246155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246155).length < 2 ^ (prefixWord ++ tailWord_246155).sum := by decide
  have hdescent : baseEnd_246155 < baseStart_246155 := by decide
  rcases family_descends (prefixWord ++ tailWord_246155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246324 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_246324 : Nat := 118140960795 + 246324 * 2 ^ 59
def prefixEnd_246324 : Nat := 4983230072969 + 3 ^ 40 * 246324 * 2
def baseEnd_246324 : Nat := 56214492772533106629859

theorem tailTrace_246324 : CollatzResearch.WordTrace tailWord_246324 prefixEnd_246324 56214492772533106629859 := by
  unfold tailWord_246324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492087179808845817521013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5989449573078461090028017 4492087179808845817521013)
  ·
    refine ⟨421133173107079295392595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4492087179808845817521013 421133173107079295392595)
    ·
      refine ⟨631699759660618943088893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421133173107079295392595 631699759660618943088893)
      ·
        refine ⟨236887409872732103658335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631699759660618943088893 236887409872732103658335)
        ·
          refine ⟨355331114809098155487503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236887409872732103658335 355331114809098155487503)
          ·
            refine ⟨532996672213647233231255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355331114809098155487503 532996672213647233231255)
            ·
              refine ⟨799495008320470849846883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532996672213647233231255 799495008320470849846883)
              ·
                refine ⟨1199242512480706274770325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799495008320470849846883 1199242512480706274770325)
                ·
                  refine ⟨56214492772533106629859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1199242512480706274770325 56214492772533106629859)
                  ·
                    rfl

theorem cell21_246324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_246324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246324 prefixEnd_246324 := by exact prefixLift 246324
  have htrace : WordTrace (prefixWord ++ tailWord_246324) baseStart_246324 baseEnd_246324 := by
    simpa [prefixWord, tailWord_246324, baseEnd_246324] using wordTrace_append hprefix tailTrace_246324
  have hstable : (prefixWord ++ tailWord_246324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246324).length < 2 ^ (prefixWord ++ tailWord_246324).sum := by decide
  have hdescent : baseEnd_246324 < baseStart_246324 := by decide
  rcases family_descends (prefixWord ++ tailWord_246324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246335 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_246335 : Nat := 118140960795 + 246335 * 2 ^ 59
def prefixEnd_246335 : Nat := 4983230072969 + 3 ^ 40 * 246335 * 2
def baseEnd_246335 : Nat := 56217003122399531946503

theorem tailTrace_246335 : CollatzResearch.WordTrace tailWord_246335 prefixEnd_246335 56217003122399531946503 := by
  unfold tailWord_246335
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984575562577840513692459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989717041718560342461639 8984575562577840513692459)
  ·
    refine ⟨13476863343866760770538689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8984575562577840513692459 13476863343866760770538689)
    ·
      refine ⟨10107647507900070577904017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13476863343866760770538689 10107647507900070577904017)
      ·
        refine ⟨7580735630925052933428013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10107647507900070577904017 7580735630925052933428013)
        ·
          refine ⟨2842775861596894850035505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7580735630925052933428013 2842775861596894850035505)
          ·
            refine ⟨2132081896197671137526629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2842775861596894850035505 2132081896197671137526629)
            ·
              refine ⟨399765355537063338286243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2132081896197671137526629 399765355537063338286243)
              ·
                refine ⟨599648033305595007429365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399765355537063338286243 599648033305595007429365)
                ·
                  refine ⟨56217003122399531946503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599648033305595007429365 56217003122399531946503)
                  ·
                    rfl

theorem cell21_246335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_246335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246335 prefixEnd_246335 := by exact prefixLift 246335
  have htrace : WordTrace (prefixWord ++ tailWord_246335) baseStart_246335 baseEnd_246335 := by
    simpa [prefixWord, tailWord_246335, baseEnd_246335] using wordTrace_append hprefix tailTrace_246335
  have hstable : (prefixWord ++ tailWord_246335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246335).length < 2 ^ (prefixWord ++ tailWord_246335).sum := by decide
  have hdescent : baseEnd_246335 < baseStart_246335 := by decide
  rcases family_descends (prefixWord ++ tailWord_246335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246369 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 3]
def baseStart_246369 : Nat := 118140960795 + 246369 * 2 ^ 59
def prefixEnd_246369 : Nat := 4983230072969 + 3 ^ 40 * 246369 * 2
def baseEnd_246369 : Nat := 56224762385623028379767

theorem tailTrace_246369 : CollatzResearch.WordTrace tailWord_246369 prefixEnd_246369 56224762385623028379767 := by
  unfold tailWord_246369
  simp only [CollatzResearch.WordTrace]
  refine ⟨8985815644454664320430161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5990543762969776213620107 8985815644454664320430161)
  ·
    refine ⟨6739361733340998240322621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8985815644454664320430161 6739361733340998240322621)
    ·
      refine ⟨2527260650002874340120983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6739361733340998240322621 2527260650002874340120983)
      ·
        refine ⟨3790890975004311510181475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527260650002874340120983 3790890975004311510181475)
        ·
          refine ⟨5686336462506467265272213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790890975004311510181475 5686336462506467265272213)
          ·
            refine ⟨266547021679990653059635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5686336462506467265272213 266547021679990653059635)
            ·
              refine ⟨399820532519985979589453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266547021679990653059635 399820532519985979589453)
              ·
                refine ⟨149932699694994742346045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399820532519985979589453 149932699694994742346045)
                ·
                  refine ⟨56224762385623028379767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149932699694994742346045 56224762385623028379767)
                  ·
                    rfl

theorem cell21_246369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_246369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246369 prefixEnd_246369 := by exact prefixLift 246369
  have htrace : WordTrace (prefixWord ++ tailWord_246369) baseStart_246369 baseEnd_246369 := by
    simpa [prefixWord, tailWord_246369, baseEnd_246369] using wordTrace_append hprefix tailTrace_246369
  have hstable : (prefixWord ++ tailWord_246369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246369).length < 2 ^ (prefixWord ++ tailWord_246369).sum := by decide
  have hdescent : baseEnd_246369 < baseStart_246369 := by decide
  rcases family_descends (prefixWord ++ tailWord_246369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246386 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_246386 : Nat := 118140960795 + 246386 * 2 ^ 59
def prefixEnd_246386 : Nat := 4983230072969 + 3 ^ 40 * 246386 * 2
def baseEnd_246386 : Nat := 56228642017234776596399

theorem tailTrace_246386 : CollatzResearch.WordTrace tailWord_246386 prefixEnd_246386 56228642017234776596399 := by
  unfold tailWord_246386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246608921348269055949753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5990957123595384149199341 2246608921348269055949753)
  ·
    refine ⟨1684956691011201791962315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2246608921348269055949753 1684956691011201791962315)
    ·
      refine ⟨2527435036516802687943473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684956691011201791962315 2527435036516802687943473)
      ·
        refine ⟨1895576277387602015957605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2527435036516802687943473 1895576277387602015957605)
        ·
          refine ⟨355420552010175377992051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1895576277387602015957605 355420552010175377992051)
          ·
            refine ⟨533130828015263066988077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355420552010175377992051 533130828015263066988077)
            ·
              refine ⟨199924060505723650120529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533130828015263066988077 199924060505723650120529)
              ·
                refine ⟨149943045379292737590397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199924060505723650120529 149943045379292737590397)
                ·
                  refine ⟨56228642017234776596399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149943045379292737590397 56228642017234776596399)
                  ·
                    rfl

theorem cell21_246386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_246386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246386 prefixEnd_246386 := by exact prefixLift 246386
  have htrace : WordTrace (prefixWord ++ tailWord_246386) baseStart_246386 baseEnd_246386 := by
    simpa [prefixWord, tailWord_246386, baseEnd_246386] using wordTrace_append hprefix tailTrace_246386
  have hstable : (prefixWord ++ tailWord_246386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246386).length < 2 ^ (prefixWord ++ tailWord_246386).sum := by decide
  have hdescent : baseEnd_246386 < baseStart_246386 := by decide
  rcases family_descends (prefixWord ++ tailWord_246386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246397 : List Nat := [1, 4, 1, 1, 5, 1, 2, 6]
def baseStart_246397 : Nat := 118140960795 + 246397 * 2 ^ 59
def prefixEnd_246397 : Nat := 4983230072969 + 3 ^ 40 * 246397 * 2
def baseEnd_246397 : Nat := 18743717455700400637681

theorem tailTrace_246397 : CollatzResearch.WordTrace tailWord_246397 prefixEnd_246397 18743717455700400637681 := by
  unfold tailWord_246397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986836888353225102449445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5991224592235483401632963 8986836888353225102449445)
  ·
    refine ⟨1685031916566229706709271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8986836888353225102449445 1685031916566229706709271)
    ·
      refine ⟨2527547874849344560063907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685031916566229706709271 2527547874849344560063907)
      ·
        refine ⟨3791321812274016840095861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527547874849344560063907 3791321812274016840095861)
        ·
          refine ⟨355436419900689078758987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3791321812274016840095861 355436419900689078758987)
          ·
            refine ⟨533154629851033618138481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355436419900689078758987 533154629851033618138481)
            ·
              refine ⟨399865972388275213603861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533154629851033618138481 399865972388275213603861)
              ·
                refine ⟨18743717455700400637681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399865972388275213603861 18743717455700400637681)
                ·
                  rfl

theorem cell21_246397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_246397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246397 prefixEnd_246397 := by exact prefixLift 246397
  have htrace : WordTrace (prefixWord ++ tailWord_246397) baseStart_246397 baseEnd_246397 := by
    simpa [prefixWord, tailWord_246397, baseEnd_246397] using wordTrace_append hprefix tailTrace_246397
  have hstable : (prefixWord ++ tailWord_246397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246397).length < 2 ^ (prefixWord ++ tailWord_246397).sum := by decide
  have hdescent : baseEnd_246397 < baseStart_246397 := by decide
  rcases family_descends (prefixWord ++ tailWord_246397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246445 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 3]
def baseStart_246445 : Nat := 118140960795 + 246445 * 2 ^ 59
def prefixEnd_246445 : Nat := 4983230072969 + 3 ^ 40 * 246445 * 2
def baseEnd_246445 : Nat := 56242106621063785112945

theorem tailTrace_246445 : CollatzResearch.WordTrace tailWord_246445 prefixEnd_246445 56242106621063785112945 := by
  unfold tailWord_246445
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988587592179329300196789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5992391728119552866797859 8988587592179329300196789)
  ·
    refine ⟨842680086766812121893449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8988587592179329300196789 842680086766812121893449)
    ·
      refine ⟨632010065075109091420087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842680086766812121893449 632010065075109091420087)
      ·
        refine ⟨948015097612663637130131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632010065075109091420087 948015097612663637130131)
        ·
          refine ⟨1422022646418995455695197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948015097612663637130131 1422022646418995455695197)
          ·
            refine ⟨533258492407123295885699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1422022646418995455695197 533258492407123295885699)
            ·
              refine ⟨799887738610684943828549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533258492407123295885699 799887738610684943828549)
              ·
                refine ⟨149978950989503426967853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799887738610684943828549 149978950989503426967853)
                ·
                  refine ⟨56242106621063785112945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149978950989503426967853 56242106621063785112945)
                  ·
                    rfl

theorem cell21_246445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_246445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246445 prefixEnd_246445 := by exact prefixLift 246445
  have htrace : WordTrace (prefixWord ++ tailWord_246445) baseStart_246445 baseEnd_246445 := by
    simpa [prefixWord, tailWord_246445, baseEnd_246445] using wordTrace_append hprefix tailTrace_246445
  have hstable : (prefixWord ++ tailWord_246445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246445).length < 2 ^ (prefixWord ++ tailWord_246445).sum := by decide
  have hdescent : baseEnd_246445 < baseStart_246445 := by decide
  rcases family_descends (prefixWord ++ tailWord_246445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246504 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_246504 : Nat := 118140960795 + 246504 * 2 ^ 59
def prefixEnd_246504 : Nat := 4983230072969 + 3 ^ 40 * 246504 * 2
def baseEnd_246504 : Nat := 56255571224892793629491

theorem tailTrace_246504 : CollatzResearch.WordTrace tailWord_246504 prefixEnd_246504 56255571224892793629491 := by
  unfold tailWord_246504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495369749482791188297283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5993826332643721584396377 4495369749482791188297283)
  ·
    refine ⟨6743054624224186782445925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4495369749482791188297283 6743054624224186782445925)
    ·
      refine ⟨1264322742042035021708611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6743054624224186782445925 1264322742042035021708611)
      ·
        refine ⟨1896484113063052532562917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264322742042035021708611 1896484113063052532562917)
        ·
          refine ⟨355590771199322349855547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1896484113063052532562917 355590771199322349855547)
          ·
            refine ⟨533386156798983524783321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355590771199322349855547 533386156798983524783321)
            ·
              refine ⟨400039617599237643587491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533386156798983524783321 400039617599237643587491)
              ·
                refine ⟨600059426398856465381237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400039617599237643587491 600059426398856465381237)
                ·
                  refine ⟨56255571224892793629491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 600059426398856465381237 56255571224892793629491)
                  ·
                    rfl

theorem cell21_246504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_246504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246504 prefixEnd_246504 := by exact prefixLift 246504
  have htrace : WordTrace (prefixWord ++ tailWord_246504) baseStart_246504 baseEnd_246504 := by
    simpa [prefixWord, tailWord_246504, baseEnd_246504] using wordTrace_append hprefix tailTrace_246504
  have hstable : (prefixWord ++ tailWord_246504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246504).length < 2 ^ (prefixWord ++ tailWord_246504).sum := by decide
  have hdescent : baseEnd_246504 < baseStart_246504 := by decide
  rcases family_descends (prefixWord ++ tailWord_246504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246515 : List Nat := [1, 1, 1, 2, 2, 3, 1, 10]
def baseStart_246515 : Nat := 118140960795 + 246515 * 2 ^ 59
def prefixEnd_246515 : Nat := 4983230072969 + 3 ^ 40 * 246515 * 2
def baseEnd_246515 : Nat := 18752693858253072982045

theorem tailTrace_246515 : CollatzResearch.WordTrace tailWord_246515 prefixEnd_246515 18752693858253072982045 := by
  unfold tailWord_246515
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991140701925731255244999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5994093801283820836829999 8991140701925731255244999)
  ·
    refine ⟨13486711052888596882867499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8991140701925731255244999 13486711052888596882867499)
    ·
      refine ⟨20230066579332895324301249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13486711052888596882867499 20230066579332895324301249)
      ·
        refine ⟨15172549934499671493225937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20230066579332895324301249 15172549934499671493225937)
        ·
          refine ⟨11379412450874753619919453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15172549934499671493225937 11379412450874753619919453)
          ·
            refine ⟨4267279669078032607469795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11379412450874753619919453 4267279669078032607469795)
            ·
              refine ⟨6400919503617048911204693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267279669078032607469795 6400919503617048911204693)
              ·
                refine ⟨18752693858253072982045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6400919503617048911204693 18752693858253072982045)
                ·
                  rfl

theorem cell21_246515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_246515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246515 prefixEnd_246515 := by exact prefixLift 246515
  have htrace : WordTrace (prefixWord ++ tailWord_246515) baseStart_246515 baseEnd_246515 := by
    simpa [prefixWord, tailWord_246515, baseEnd_246515] using wordTrace_append hprefix tailTrace_246515
  have hstable : (prefixWord ++ tailWord_246515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246515).length < 2 ^ (prefixWord ++ tailWord_246515).sum := by decide
  have hdescent : baseEnd_246515 < baseStart_246515 := by decide
  rcases family_descends (prefixWord ++ tailWord_246515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246532 : List Nat := [2, 3, 2, 2, 1, 1, 3, 7]
def baseStart_246532 : Nat := 118140960795 + 246532 * 2 ^ 59
def prefixEnd_246532 : Nat := 4983230072969 + 3 ^ 40 * 246532 * 2
def baseEnd_246532 : Nat := 18753987068790322387589

theorem tailTrace_246532 : CollatzResearch.WordTrace tailWord_246532 prefixEnd_246532 18753987068790322387589 := by
  unfold tailWord_246532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495880371432071579306925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5994507161909428772409233 4495880371432071579306925)
  ·
    refine ⟨1685955139287026842240097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4495880371432071579306925 1685955139287026842240097)
    ·
      refine ⟨1264466354465270131680073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1685955139287026842240097 1264466354465270131680073)
      ·
        refine ⟨948349765848952598760055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264466354465270131680073 948349765848952598760055)
        ·
          refine ⟨1422524648773428898140083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948349765848952598760055 1422524648773428898140083)
          ·
            refine ⟨2133786973160143347210125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422524648773428898140083 2133786973160143347210125)
            ·
              refine ⟨800170114935053755203797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133786973160143347210125 800170114935053755203797)
              ·
                refine ⟨18753987068790322387589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 800170114935053755203797 18753987068790322387589)
                ·
                  rfl

theorem cell21_246532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_246532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246532 prefixEnd_246532 := by exact prefixLift 246532
  have htrace : WordTrace (prefixWord ++ tailWord_246532) baseStart_246532 baseEnd_246532 := by
    simpa [prefixWord, tailWord_246532, baseEnd_246532] using wordTrace_append hprefix tailTrace_246532
  have hstable : (prefixWord ++ tailWord_246532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246532).length < 2 ^ (prefixWord ++ tailWord_246532).sum := by decide
  have hdescent : baseEnd_246532 < baseStart_246532 := by decide
  rcases family_descends (prefixWord ++ tailWord_246532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246687 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 4]
def baseStart_246687 : Nat := 118140960795 + 246687 * 2 ^ 59
def prefixEnd_246687 : Nat := 4983230072969 + 3 ^ 40 * 246687 * 2
def baseEnd_246687 : Nat := 56297334318125142079117

theorem tailTrace_246687 : CollatzResearch.WordTrace tailWord_246687 prefixEnd_246687 56297334318125142079117 := by
  unfold tailWord_246687
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997414057302604630506315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5998276038201736420337543 8997414057302604630506315)
  ·
    refine ⟨13496121085953906945759473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8997414057302604630506315 13496121085953906945759473)
    ·
      refine ⟨10122090814465430209319605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13496121085953906945759473 10122090814465430209319605)
      ·
        refine ⟨948946013856134082123713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10122090814465430209319605 948946013856134082123713)
        ·
          refine ⟨711709510392100561592785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948946013856134082123713 711709510392100561592785)
          ·
            refine ⟨533782132794075421194589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711709510392100561592785 533782132794075421194589)
            ·
              refine ⟨200168299797778282947971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533782132794075421194589 200168299797778282947971)
              ·
                refine ⟨300252449696667424421957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200168299797778282947971 300252449696667424421957)
                ·
                  refine ⟨56297334318125142079117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300252449696667424421957 56297334318125142079117)
                  ·
                    rfl

theorem cell21_246687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4].length) (baseStart_246687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246687 prefixEnd_246687 := by exact prefixLift 246687
  have htrace : WordTrace (prefixWord ++ tailWord_246687) baseStart_246687 baseEnd_246687 := by
    simpa [prefixWord, tailWord_246687, baseEnd_246687] using wordTrace_append hprefix tailTrace_246687
  have hstable : (prefixWord ++ tailWord_246687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246687).length < 2 ^ (prefixWord ++ tailWord_246687).sum := by decide
  have hdescent : baseEnd_246687 < baseStart_246687 := by decide
  rcases family_descends (prefixWord ++ tailWord_246687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246746 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_246746 : Nat := 118140960795 + 246746 * 2 ^ 59
def prefixEnd_246746 : Nat := 4983230072969 + 3 ^ 40 * 246746 * 2
def baseEnd_246746 : Nat := 56310798921954150595663

theorem tailTrace_246746 : CollatzResearch.WordTrace tailWord_246746 prefixEnd_246746 56310798921954150595663 := by
  unfold tailWord_246746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249891491022214426726023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5999710642725905137936061 2249891491022214426726023)
  ·
    refine ⟨3374837236533321640089035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249891491022214426726023 3374837236533321640089035)
    ·
      refine ⟨5062255854799982460133553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374837236533321640089035 5062255854799982460133553)
      ·
        refine ⟨3796691891099986845100165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062255854799982460133553 3796691891099986845100165)
        ·
          refine ⟨711879729581247533456281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3796691891099986845100165 711879729581247533456281)
          ·
            refine ⟨533909797185935650092211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711879729581247533456281 533909797185935650092211)
            ·
              refine ⟨800864695778903475138317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533909797185935650092211 800864695778903475138317)
              ·
                refine ⟨300324260917088803176869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 800864695778903475138317 300324260917088803176869)
                ·
                  refine ⟨56310798921954150595663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300324260917088803176869 56310798921954150595663)
                  ·
                    rfl

theorem cell21_246746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_246746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246746 prefixEnd_246746 := by exact prefixLift 246746
  have htrace : WordTrace (prefixWord ++ tailWord_246746) baseStart_246746 baseEnd_246746 := by
    simpa [prefixWord, tailWord_246746, baseEnd_246746] using wordTrace_append hprefix tailTrace_246746
  have hstable : (prefixWord ++ tailWord_246746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246746).length < 2 ^ (prefixWord ++ tailWord_246746).sum := by decide
  have hdescent : baseEnd_246746 < baseStart_246746 := by decide
  rcases family_descends (prefixWord ++ tailWord_246746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246870 : List Nat := [5, 2, 2, 1, 2, 1, 1, 7]
def baseStart_246870 : Nat := 118140960795 + 246870 * 2 ^ 59
def prefixEnd_246870 : Nat := 4983230072969 + 3 ^ 40 * 246870 * 2
def baseEnd_246870 : Nat := 18779699137119163509581

theorem tailTrace_246870 : CollatzResearch.WordTrace tailWord_246870 prefixEnd_246870 18779699137119163509581 := by
  unfold tailWord_246870
  simp only [CollatzResearch.WordTrace]
  refine ⟨562755538477476680276129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6002725743759751256278709 562755538477476680276129)
  ·
    refine ⟨422066653858107510207097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562755538477476680276129 422066653858107510207097)
    ·
      refine ⟨316549990393580632655323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422066653858107510207097 316549990393580632655323)
      ·
        refine ⟨474824985590370948982985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316549990393580632655323 474824985590370948982985)
        ·
          refine ⟨356118739192778211737239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474824985590370948982985 356118739192778211737239)
          ·
            refine ⟨534178108789167317605859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356118739192778211737239 534178108789167317605859)
            ·
              refine ⟨801267163183750976408789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534178108789167317605859 801267163183750976408789)
              ·
                refine ⟨18779699137119163509581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 801267163183750976408789 18779699137119163509581)
                ·
                  rfl

theorem cell21_246870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_246870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246870 prefixEnd_246870 := by exact prefixLift 246870
  have htrace : WordTrace (prefixWord ++ tailWord_246870) baseStart_246870 baseEnd_246870 := by
    simpa [prefixWord, tailWord_246870, baseEnd_246870] using wordTrace_append hprefix tailTrace_246870
  have hstable : (prefixWord ++ tailWord_246870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246870).length < 2 ^ (prefixWord ++ tailWord_246870).sum := by decide
  have hdescent : baseEnd_246870 < baseStart_246870 := by decide
  rcases family_descends (prefixWord ++ tailWord_246870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246901 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 5]
def baseStart_246901 : Nat := 118140960795 + 246901 * 2 ^ 59
def prefixEnd_246901 : Nat := 4983230072969 + 3 ^ 40 * 246901 * 2
def baseEnd_246901 : Nat := 56346172033708325512013

theorem tailTrace_246901 : CollatzResearch.WordTrace tailWord_246901 prefixEnd_246901 56346172033708325512013 := by
  unfold tailWord_246901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005219278527319178796557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6003479519018212785864371 9005219278527319178796557)
  ·
    refine ⟨3376957229447744692048709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9005219278527319178796557 3376957229447744692048709)
    ·
      refine ⟨633179480521452129759133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3376957229447744692048709 633179480521452129759133)
      ·
        refine ⟨237442305195544548659675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 633179480521452129759133 237442305195544548659675)
        ·
          refine ⟨356163457793316822989513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237442305195544548659675 356163457793316822989513)
          ·
            refine ⟨267122593344987617242135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356163457793316822989513 267122593344987617242135)
            ·
              refine ⟨400683890017481425863203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267122593344987617242135 400683890017481425863203)
              ·
                refine ⟨601025835026222138794805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400683890017481425863203 601025835026222138794805)
                ·
                  refine ⟨56346172033708325512013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601025835026222138794805 56346172033708325512013)
                  ·
                    rfl

theorem cell21_246901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_246901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246901 prefixEnd_246901 := by exact prefixLift 246901
  have htrace : WordTrace (prefixWord ++ tailWord_246901) baseStart_246901 baseEnd_246901 := by
    simpa [prefixWord, tailWord_246901, baseEnd_246901] using wordTrace_append hprefix tailTrace_246901
  have hstable : (prefixWord ++ tailWord_246901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246901).length < 2 ^ (prefixWord ++ tailWord_246901).sum := by decide
  have hdescent : baseEnd_246901 < baseStart_246901 := by decide
  rcases family_descends (prefixWord ++ tailWord_246901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246974 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_246974 : Nat := 118140960795 + 246974 * 2 ^ 59
def prefixEnd_246974 : Nat := 4983230072969 + 3 ^ 40 * 246974 * 2
def baseEnd_246974 : Nat := 56362831628276420795197

theorem tailTrace_246974 : CollatzResearch.WordTrace tailWord_246974 prefixEnd_246974 56362831628276420795197 := by
  unfold tailWord_246974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125985225907856580775497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6005254538175235097469317 1125985225907856580775497)
  ·
    refine ⟨844488919430892435581623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1125985225907856580775497 844488919430892435581623)
    ·
      refine ⟨1266733379146338653372435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844488919430892435581623 1266733379146338653372435)
      ·
        refine ⟨1900100068719507980058653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266733379146338653372435 1900100068719507980058653)
        ·
          refine ⟨712537525769815492521995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1900100068719507980058653 712537525769815492521995)
          ·
            refine ⟨1068806288654723238782993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712537525769815492521995 1068806288654723238782993)
            ·
              refine ⟨801604716491042429087245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068806288654723238782993 801604716491042429087245)
              ·
                refine ⟨300601768684140910907717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801604716491042429087245 300601768684140910907717)
                ·
                  refine ⟨56362831628276420795197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300601768684140910907717 56362831628276420795197)
                  ·
                    rfl

theorem cell21_246974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_246974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_246974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_246974 prefixEnd_246974 := by exact prefixLift 246974
  have htrace : WordTrace (prefixWord ++ tailWord_246974) baseStart_246974 baseEnd_246974 := by
    simpa [prefixWord, tailWord_246974, baseEnd_246974] using wordTrace_append hprefix tailTrace_246974
  have hstable : (prefixWord ++ tailWord_246974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246974).length < 2 ^ (prefixWord ++ tailWord_246974).sum := by decide
  have hdescent : baseEnd_246974 < baseStart_246974 := by decide
  rcases family_descends (prefixWord ++ tailWord_246974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247019 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 3]
def baseStart_247019 : Nat := 118140960795 + 247019 * 2 ^ 59
def prefixEnd_247019 : Nat := 4983230072969 + 3 ^ 40 * 247019 * 2
def baseEnd_247019 : Nat := 56373101241366342545105

theorem tailTrace_247019 : CollatzResearch.WordTrace tailWord_247019 prefixEnd_247019 56373101241366342545105 := by
  unfold tailWord_247019
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009523092099825331592111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6006348728066550221061407 9009523092099825331592111)
  ·
    refine ⟨13514284638149737997388167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9009523092099825331592111 13514284638149737997388167)
    ·
      refine ⟨20271426957224606996082251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13514284638149737997388167 20271426957224606996082251)
      ·
        refine ⟨30407140435836910494123377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271426957224606996082251 30407140435836910494123377)
        ·
          refine ⟨22805355326877682870592533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30407140435836910494123377 22805355326877682870592533)
          ·
            refine ⟨1069001030947391384559025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22805355326877682870592533 1069001030947391384559025)
            ·
              refine ⟨801750773210543538419269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069001030947391384559025 801750773210543538419269)
              ·
                refine ⟨150328269976976913453613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801750773210543538419269 150328269976976913453613)
                ·
                  refine ⟨56373101241366342545105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150328269976976913453613 56373101241366342545105)
                  ·
                    rfl

theorem cell21_247019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3].length) (baseStart_247019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247019 prefixEnd_247019 := by exact prefixLift 247019
  have htrace : WordTrace (prefixWord ++ tailWord_247019) baseStart_247019 baseEnd_247019 := by
    simpa [prefixWord, tailWord_247019, baseEnd_247019] using wordTrace_append hprefix tailTrace_247019
  have hstable : (prefixWord ++ tailWord_247019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247019).length < 2 ^ (prefixWord ++ tailWord_247019).sum := by decide
  have hdescent : baseEnd_247019 < baseStart_247019 := by decide
  rcases family_descends (prefixWord ++ tailWord_247019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247070 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_247070 : Nat := 118140960795 + 247070 * 2 ^ 59
def prefixEnd_247070 : Nat := 4983230072969 + 3 ^ 40 * 247070 * 2
def baseEnd_247070 : Nat := 56384740136201587195001

theorem tailTrace_247070 : CollatzResearch.WordTrace tailWord_247070 prefixEnd_247070 56384740136201587195001 := by
  unfold tailWord_247070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126422901864382630212333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6007588809943374027799109 1126422901864382630212333)
  ·
    refine ⟨422408588199143486329625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1126422901864382630212333 422408588199143486329625)
    ·
      refine ⟨316806441149357614747219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422408588199143486329625 316806441149357614747219)
      ·
        refine ⟨475209661724036422120829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316806441149357614747219 475209661724036422120829)
        ·
          refine ⟨178203623146513658295311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475209661724036422120829 178203623146513658295311)
          ·
            refine ⟨267305434719770487442967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178203623146513658295311 267305434719770487442967)
            ·
              refine ⟨400958152079655731164451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267305434719770487442967 400958152079655731164451)
              ·
                refine ⟨601437228119483596746677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400958152079655731164451 601437228119483596746677)
                ·
                  refine ⟨56384740136201587195001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601437228119483596746677 56384740136201587195001)
                  ·
                    rfl

theorem cell21_247070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_247070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247070 prefixEnd_247070 := by exact prefixLift 247070
  have htrace : WordTrace (prefixWord ++ tailWord_247070) baseStart_247070 baseEnd_247070 := by
    simpa [prefixWord, tailWord_247070, baseEnd_247070] using wordTrace_append hprefix tailTrace_247070
  have hstable : (prefixWord ++ tailWord_247070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247070).length < 2 ^ (prefixWord ++ tailWord_247070).sum := by decide
  have hdescent : baseEnd_247070 < baseStart_247070 := by decide
  rcases family_descends (prefixWord ++ tailWord_247070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247137 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_247137 : Nat := 118140960795 + 247137 * 2 ^ 59
def prefixEnd_247137 : Nat := 4983230072969 + 3 ^ 40 * 247137 * 2
def baseEnd_247137 : Nat := 56400030449024359578197

theorem tailTrace_247137 : CollatzResearch.WordTrace tailWord_247137 prefixEnd_247137 56400030449024359578197 := by
  unfold tailWord_247137
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013826905672331484387665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6009217937114887656258443 9013826905672331484387665)
  ·
    refine ⟨6760370179254248613290749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9013826905672331484387665 6760370179254248613290749)
    ·
      refine ⟨2535138817220343229984031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6760370179254248613290749 2535138817220343229984031)
      ·
        refine ⟨3802708225830514844976047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535138817220343229984031 3802708225830514844976047)
        ·
          refine ⟨5704062338745772267464071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802708225830514844976047 5704062338745772267464071)
          ·
            refine ⟨8556093508118658401196107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704062338745772267464071 8556093508118658401196107)
            ·
              refine ⟨12834140262177987601794161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556093508118658401196107 12834140262177987601794161)
              ·
                refine ⟨9625605196633490701345621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12834140262177987601794161 9625605196633490701345621)
                ·
                  refine ⟨56400030449024359578197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9625605196633490701345621 56400030449024359578197)
                  ·
                    rfl

theorem cell21_247137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_247137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247137 prefixEnd_247137 := by exact prefixLift 247137
  have htrace : WordTrace (prefixWord ++ tailWord_247137) baseStart_247137 baseEnd_247137 := by
    simpa [prefixWord, tailWord_247137, baseEnd_247137] using wordTrace_append hprefix tailTrace_247137
  have hstable : (prefixWord ++ tailWord_247137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247137).length < 2 ^ (prefixWord ++ tailWord_247137).sum := by decide
  have hdescent : baseEnd_247137 < baseStart_247137 := by decide
  rcases family_descends (prefixWord ++ tailWord_247137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247140 : List Nat := [2, 3, 1, 1, 3, 4, 1, 6]
def baseStart_247140 : Nat := 118140960795 + 247140 * 2 ^ 59
def prefixEnd_247140 : Nat := 4983230072969 + 3 ^ 40 * 247140 * 2
def baseEnd_247140 : Nat := 18800238363299007009397

theorem tailTrace_247140 : CollatzResearch.WordTrace tailWord_247140 prefixEnd_247140 18800238363299007009397 := by
  unfold tailWord_247140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506968162330731498373437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6009290883107641997831249 4506968162330731498373437)
  ·
    refine ⟨1690113060874024311890039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4506968162330731498373437 1690113060874024311890039)
    ·
      refine ⟨2535169591311036467835059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690113060874024311890039 2535169591311036467835059)
      ·
        refine ⟨3802754386966554701752589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535169591311036467835059 3802754386966554701752589)
        ·
          refine ⟨1426032895112458013157221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3802754386966554701752589 1426032895112458013157221)
          ·
            refine ⟨267381167833585877466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1426032895112458013157221 267381167833585877466979)
            ·
              refine ⟨401071751750378816200469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267381167833585877466979 401071751750378816200469)
              ·
                refine ⟨18800238363299007009397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401071751750378816200469 18800238363299007009397)
                ·
                  rfl

theorem cell21_247140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_247140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247140 prefixEnd_247140 := by exact prefixLift 247140
  have htrace : WordTrace (prefixWord ++ tailWord_247140) baseStart_247140 baseEnd_247140 := by
    simpa [prefixWord, tailWord_247140, baseEnd_247140] using wordTrace_append hprefix tailTrace_247140
  have hstable : (prefixWord ++ tailWord_247140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247140).length < 2 ^ (prefixWord ++ tailWord_247140).sum := by decide
  have hdescent : baseEnd_247140 < baseStart_247140 := by decide
  rcases family_descends (prefixWord ++ tailWord_247140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247154 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_247154 : Nat := 118140960795 + 247154 * 2 ^ 59
def prefixEnd_247154 : Nat := 4983230072969 + 3 ^ 40 * 247154 * 2
def baseEnd_247154 : Nat := 56403910080636107794829

theorem tailTrace_247154 : CollatzResearch.WordTrace tailWord_247154 prefixEnd_247154 56403910080636107794829 := by
  unfold tailWord_247154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253611736652685846939129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6009631297740495591837677 2253611736652685846939129)
  ·
    refine ⟨1690208802489514385204347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2253611736652685846939129 1690208802489514385204347)
    ·
      refine ⟨2535313203734271577806521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690208802489514385204347 2535313203734271577806521)
      ·
        refine ⟨1901484902800703683354891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535313203734271577806521 1901484902800703683354891)
        ·
          refine ⟨2852227354201055525032337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901484902800703683354891 2852227354201055525032337)
          ·
            refine ⟨2139170515650791643774253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852227354201055525032337 2139170515650791643774253)
            ·
              refine ⟨802188943369046866415345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2139170515650791643774253 802188943369046866415345)
              ·
                refine ⟨601641707526785149811509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802188943369046866415345 601641707526785149811509)
                ·
                  refine ⟨56403910080636107794829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601641707526785149811509 56403910080636107794829)
                  ·
                    rfl

theorem cell21_247154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_247154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247154 prefixEnd_247154 := by exact prefixLift 247154
  have htrace : WordTrace (prefixWord ++ tailWord_247154) baseStart_247154 baseEnd_247154 := by
    simpa [prefixWord, tailWord_247154, baseEnd_247154] using wordTrace_append hprefix tailTrace_247154
  have hstable : (prefixWord ++ tailWord_247154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247154).length < 2 ^ (prefixWord ++ tailWord_247154).sum := by decide
  have hdescent : baseEnd_247154 < baseStart_247154 := by decide
  rcases family_descends (prefixWord ++ tailWord_247154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247157 : List Nat := [1, 3, 4, 1, 3, 1, 3, 5]
def baseStart_247157 : Nat := 118140960795 + 247157 * 2 ^ 59
def prefixEnd_247157 : Nat := 4983230072969 + 3 ^ 40 * 247157 * 2
def baseEnd_247157 : Nat := 18801531573836256414941

theorem tailTrace_247157 : CollatzResearch.WordTrace tailWord_247157 prefixEnd_247157 18801531573836256414941 := by
  unfold tailWord_247157
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014556365599874900115725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6009704243733249933410483 9014556365599874900115725)
  ·
    refine ⟨3380458637099953087543397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9014556365599874900115725 3380458637099953087543397)
    ·
      refine ⟨633835994456241203914387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3380458637099953087543397 633835994456241203914387)
      ·
        refine ⟨950753991684361805871581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633835994456241203914387 950753991684361805871581)
        ·
          refine ⟨356532746881635677201843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 950753991684361805871581 356532746881635677201843)
          ·
            refine ⟨534799120322453515802765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356532746881635677201843 534799120322453515802765)
            ·
              refine ⟨200549670120920068426037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534799120322453515802765 200549670120920068426037)
              ·
                refine ⟨18801531573836256414941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200549670120920068426037 18801531573836256414941)
                ·
                  rfl

theorem cell21_247157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 5].length) (baseStart_247157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247157 prefixEnd_247157 := by exact prefixLift 247157
  have htrace : WordTrace (prefixWord ++ tailWord_247157) baseStart_247157 baseEnd_247157 := by
    simpa [prefixWord, tailWord_247157, baseEnd_247157] using wordTrace_append hprefix tailTrace_247157
  have hstable : (prefixWord ++ tailWord_247157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247157).length < 2 ^ (prefixWord ++ tailWord_247157).sum := by decide
  have hdescent : baseEnd_247157 < baseStart_247157 := by decide
  rcases family_descends (prefixWord ++ tailWord_247157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247171 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 3]
def baseStart_247171 : Nat := 118140960795 + 247171 * 2 ^ 59
def prefixEnd_247171 : Nat := 4983230072969 + 3 ^ 40 * 247171 * 2
def baseEnd_247171 : Nat := 56407789712247856011461

theorem tailTrace_247171 : CollatzResearch.WordTrace tailWord_247171 prefixEnd_247171 56407789712247856011461 := by
  unfold tailWord_247171
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015066987549155291125367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6010044658366103527416911 9015066987549155291125367)
  ·
    refine ⟨13522600481323732936688051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015066987549155291125367 13522600481323732936688051)
    ·
      refine ⟨20283900721985599405032077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13522600481323732936688051 20283900721985599405032077)
      ·
        refine ⟨7606462770744599776887029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20283900721985599405032077 7606462770744599776887029)
        ·
          refine ⟨713105884757306229083159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7606462770744599776887029 713105884757306229083159)
          ·
            refine ⟨1069658827135959343624739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713105884757306229083159 1069658827135959343624739)
            ·
              refine ⟨1604488240703939015437109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069658827135959343624739 1604488240703939015437109)
              ·
                refine ⟨150420772565994282697229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1604488240703939015437109 150420772565994282697229)
                ·
                  refine ⟨56407789712247856011461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150420772565994282697229 56407789712247856011461)
                  ·
                    rfl

theorem cell21_247171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 3].length) (baseStart_247171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247171 prefixEnd_247171 := by exact prefixLift 247171
  have htrace : WordTrace (prefixWord ++ tailWord_247171) baseStart_247171 baseEnd_247171 := by
    simpa [prefixWord, tailWord_247171, baseEnd_247171] using wordTrace_append hprefix tailTrace_247171
  have hstable : (prefixWord ++ tailWord_247171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247171).length < 2 ^ (prefixWord ++ tailWord_247171).sum := by decide
  have hdescent : baseEnd_247171 < baseStart_247171 := by decide
  rcases family_descends (prefixWord ++ tailWord_247171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247188 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_247188 : Nat := 118140960795 + 247188 * 2 ^ 59
def prefixEnd_247188 : Nat := 4983230072969 + 3 ^ 40 * 247188 * 2
def baseEnd_247188 : Nat := 56411669343859604228093

theorem tailTrace_247188 : CollatzResearch.WordTrace tailWord_247188 prefixEnd_247188 56411669343859604228093 := by
  unfold tailWord_247188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507843514243783597247109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6010458018991711462996145 4507843514243783597247109)
  ·
    refine ⟨845220658920709424483833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4507843514243783597247109 845220658920709424483833)
    ·
      refine ⟨633915494190532068362875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845220658920709424483833 633915494190532068362875)
      ·
        refine ⟨950873241285798102544313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633915494190532068362875 950873241285798102544313)
        ·
          refine ⟨713154930964348576908235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950873241285798102544313 713154930964348576908235)
          ·
            refine ⟨1069732396446522865362353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713154930964348576908235 1069732396446522865362353)
            ·
              refine ⟨802299297334892149021765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069732396446522865362353 802299297334892149021765)
              ·
                refine ⟨150431118250292277941581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802299297334892149021765 150431118250292277941581)
                ·
                  refine ⟨56411669343859604228093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150431118250292277941581 56411669343859604228093)
                  ·
                    rfl

theorem cell21_247188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_247188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247188 prefixEnd_247188 := by exact prefixLift 247188
  have htrace : WordTrace (prefixWord ++ tailWord_247188) baseStart_247188 baseEnd_247188 := by
    simpa [prefixWord, tailWord_247188, baseEnd_247188] using wordTrace_append hprefix tailTrace_247188
  have hstable : (prefixWord ++ tailWord_247188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247188).length < 2 ^ (prefixWord ++ tailWord_247188).sum := by decide
  have hdescent : baseEnd_247188 < baseStart_247188 := by decide
  rcases family_descends (prefixWord ++ tailWord_247188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247298 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_247298 : Nat := 118140960795 + 247298 * 2 ^ 59
def prefixEnd_247298 : Nat := 4983230072969 + 3 ^ 40 * 247298 * 2
def baseEnd_247298 : Nat := 56436772842523857394535

theorem tailTrace_247298 : CollatzResearch.WordTrace tailWord_247298 prefixEnd_247298 56436772842523857394535 := by
  unfold tailWord_247298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254924764522263995249637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6013132705392703987332365 2254924764522263995249637)
  ·
    refine ⟨422798393347924499109307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2254924764522263995249637 422798393347924499109307)
    ·
      refine ⟨634197590021886748663961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422798393347924499109307 634197590021886748663961)
      ·
        refine ⟨475648192516415061497971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634197590021886748663961 475648192516415061497971)
        ·
          refine ⟨713472288774622592246957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475648192516415061497971 713472288774622592246957)
          ·
            refine ⟨267552108290483472092609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713472288774622592246957 267552108290483472092609)
            ·
              refine ⟨200664081217862604069457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267552108290483472092609 200664081217862604069457)
              ·
                refine ⟨150498060913396953052093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200664081217862604069457 150498060913396953052093)
                ·
                  refine ⟨56436772842523857394535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150498060913396953052093 56436772842523857394535)
                  ·
                    rfl

theorem cell21_247298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_247298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247298 prefixEnd_247298 := by exact prefixLift 247298
  have htrace : WordTrace (prefixWord ++ tailWord_247298) baseStart_247298 baseEnd_247298 := by
    simpa [prefixWord, tailWord_247298, baseEnd_247298] using wordTrace_append hprefix tailTrace_247298
  have hstable : (prefixWord ++ tailWord_247298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247298).length < 2 ^ (prefixWord ++ tailWord_247298).sum := by decide
  have hdescent : baseEnd_247298 < baseStart_247298 := by decide
  rcases family_descends (prefixWord ++ tailWord_247298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247396 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_247396 : Nat := 118140960795 + 247396 * 2 ^ 59
def prefixEnd_247396 : Nat := 4983230072969 + 3 ^ 40 * 247396 * 2
def baseEnd_247396 : Nat := 56459137777697464761001

theorem tailTrace_247396 : CollatzResearch.WordTrace tailWord_247396 prefixEnd_247396 56459137777697464761001 := by
  unfold tailWord_247396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511636705867009359033021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6015515607822679145377361 4511636705867009359033021)
  ·
    refine ⟨1691863764700128509637383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4511636705867009359033021 1691863764700128509637383)
    ·
      refine ⟨2537795647050192764456075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691863764700128509637383 2537795647050192764456075)
      ·
        refine ⟨3806693470575289146684113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537795647050192764456075 3806693470575289146684113)
        ·
          refine ⟨2855020102931466860013085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806693470575289146684113 2855020102931466860013085)
          ·
            refine ⟨1070632538599300072504907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2855020102931466860013085 1070632538599300072504907)
            ·
              refine ⟨1605948807898950108757361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070632538599300072504907 1605948807898950108757361)
              ·
                refine ⟨1204461605924212581568021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605948807898950108757361 1204461605924212581568021)
                ·
                  refine ⟨56459137777697464761001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1204461605924212581568021 56459137777697464761001)
                  ·
                    rfl

theorem cell21_247396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_247396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247396 prefixEnd_247396 := by exact prefixLift 247396
  have htrace : WordTrace (prefixWord ++ tailWord_247396) baseStart_247396 baseEnd_247396 := by
    simpa [prefixWord, tailWord_247396, baseEnd_247396] using wordTrace_append hprefix tailTrace_247396
  have hstable : (prefixWord ++ tailWord_247396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247396).length < 2 ^ (prefixWord ++ tailWord_247396).sum := by decide
  have hdescent : baseEnd_247396 < baseStart_247396 := by decide
  rcases family_descends (prefixWord ++ tailWord_247396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247399 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 3]
def baseStart_247399 : Nat := 118140960795 + 247399 * 2 ^ 59
def prefixEnd_247399 : Nat := 4983230072969 + 3 ^ 40 * 247399 * 2
def baseEnd_247399 : Nat := 56459822418570126210995

theorem tailTrace_247399 : CollatzResearch.WordTrace tailWord_247399 prefixEnd_247399 56459822418570126210995 := by
  unfold tailWord_247399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023382830723150230425251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6015588553815433486950167 9023382830723150230425251)
  ·
    refine ⟨13535074246084725345637877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9023382830723150230425251 13535074246084725345637877)
    ·
      refine ⟨1268913210570443001153551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13535074246084725345637877 1268913210570443001153551)
      ·
        refine ⟨1903369815855664501730327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268913210570443001153551 1903369815855664501730327)
        ·
          refine ⟨2855054723783496752595491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903369815855664501730327 2855054723783496752595491)
          ·
            refine ⟨4282582085675245128893237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855054723783496752595491 4282582085675245128893237)
            ·
              refine ⟨401492070532054230833741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4282582085675245128893237 401492070532054230833741)
              ·
                refine ⟨150559526449520336562653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401492070532054230833741 150559526449520336562653)
                ·
                  refine ⟨56459822418570126210995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150559526449520336562653 56459822418570126210995)
                  ·
                    rfl

theorem cell21_247399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3].length) (baseStart_247399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247399 prefixEnd_247399 := by exact prefixLift 247399
  have htrace : WordTrace (prefixWord ++ tailWord_247399) baseStart_247399 baseEnd_247399 := by
    simpa [prefixWord, tailWord_247399, baseEnd_247399] using wordTrace_append hprefix tailTrace_247399
  have hstable : (prefixWord ++ tailWord_247399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247399).length < 2 ^ (prefixWord ++ tailWord_247399).sum := by decide
  have hdescent : baseEnd_247399 < baseStart_247399 := by decide
  rcases family_descends (prefixWord ++ tailWord_247399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247413 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_247413 : Nat := 118140960795 + 247413 * 2 ^ 59
def prefixEnd_247413 : Nat := 4983230072969 + 3 ^ 40 * 247413 * 2
def baseEnd_247413 : Nat := 56463017409309212977633

theorem tailTrace_247413 : CollatzResearch.WordTrace tailWord_247413 prefixEnd_247413 56463017409309212977633 := by
  unfold tailWord_247413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023893452672430621434893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6015928968448287080956595 9023893452672430621434893)
  ·
    refine ⟨3383960044752161483038085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9023893452672430621434893 3383960044752161483038085)
    ·
      refine ⟨634492508391030278069641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3383960044752161483038085 634492508391030278069641)
      ·
        refine ⟨475869381293272708552231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634492508391030278069641 475869381293272708552231)
        ·
          refine ⟨713804071939909062828347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475869381293272708552231 713804071939909062828347)
          ·
            refine ⟨1070706107909863594242521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713804071939909062828347 1070706107909863594242521)
            ·
              refine ⟨803029580932397695681891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070706107909863594242521 803029580932397695681891)
              ·
                refine ⟨1204544371398596543522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803029580932397695681891 1204544371398596543522837)
                ·
                  refine ⟨56463017409309212977633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1204544371398596543522837 56463017409309212977633)
                  ·
                    rfl

theorem cell21_247413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_247413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247413 prefixEnd_247413 := by exact prefixLift 247413
  have htrace : WordTrace (prefixWord ++ tailWord_247413) baseStart_247413 baseEnd_247413 := by
    simpa [prefixWord, tailWord_247413, baseEnd_247413] using wordTrace_append hprefix tailTrace_247413
  have hstable : (prefixWord ++ tailWord_247413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247413).length < 2 ^ (prefixWord ++ tailWord_247413).sum := by decide
  have hdescent : baseEnd_247413 < baseStart_247413 := by decide
  rcases family_descends (prefixWord ++ tailWord_247413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247464 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_247464 : Nat := 118140960795 + 247464 * 2 ^ 59
def prefixEnd_247464 : Nat := 4983230072969 + 3 ^ 40 * 247464 * 2
def baseEnd_247464 : Nat := 56474656304144457627529

theorem tailTrace_247464 : CollatzResearch.WordTrace tailWord_247464 prefixEnd_247464 56474656304144457627529 := by
  unfold tailWord_247464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512876787743833165770723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6017169050325110887694297 4512876787743833165770723)
  ·
    refine ⟨6769315181615749748656085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4512876787743833165770723 6769315181615749748656085)
    ·
      refine ⟨158655824569119134734127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6769315181615749748656085 158655824569119134734127)
      ·
        refine ⟨237983736853678702101191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158655824569119134734127 237983736853678702101191)
        ·
          refine ⟨356975605280518053151787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237983736853678702101191 356975605280518053151787)
          ·
            refine ⟨535463407920777079727681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356975605280518053151787 535463407920777079727681)
            ·
              refine ⟨401597555940582809795761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535463407920777079727681 401597555940582809795761)
              ·
                refine ⟨301198166955437107346821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401597555940582809795761 301198166955437107346821)
                ·
                  refine ⟨56474656304144457627529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301198166955437107346821 56474656304144457627529)
                  ·
                    rfl

theorem cell21_247464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_247464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247464 prefixEnd_247464 := by exact prefixLift 247464
  have htrace : WordTrace (prefixWord ++ tailWord_247464) baseStart_247464 baseEnd_247464 := by
    simpa [prefixWord, tailWord_247464, baseEnd_247464] using wordTrace_append hprefix tailTrace_247464
  have hstable : (prefixWord ++ tailWord_247464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247464).length < 2 ^ (prefixWord ++ tailWord_247464).sum := by decide
  have hdescent : baseEnd_247464 < baseStart_247464 := by decide
  rcases family_descends (prefixWord ++ tailWord_247464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247472 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_247472 : Nat := 118140960795 + 247472 * 2 ^ 59
def prefixEnd_247472 : Nat := 4983230072969 + 3 ^ 40 * 247472 * 2
def baseEnd_247472 : Nat := 56476482013138221494179

theorem tailTrace_247472 : CollatzResearch.WordTrace tailWord_247472 prefixEnd_247472 56476482013138221494179 := by
  unfold tailWord_247472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513022679729341848916335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6017363572972455798555113 4513022679729341848916335)
  ·
    refine ⟨6769534019594012773374503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4513022679729341848916335 6769534019594012773374503)
    ·
      refine ⟨10154301029391019160061755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769534019594012773374503 10154301029391019160061755)
      ·
        refine ⟨15231451544086528740092633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154301029391019160061755 15231451544086528740092633)
        ·
          refine ⟨11423588658064896555069475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15231451544086528740092633 11423588658064896555069475)
          ·
            refine ⟨17135382987097344832604213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11423588658064896555069475 17135382987097344832604213)
            ·
              refine ⟨1606442155040376078056645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17135382987097344832604213 1606442155040376078056645)
              ·
                refine ⟨301207904070070514635621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1606442155040376078056645 301207904070070514635621)
                ·
                  refine ⟨56476482013138221494179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301207904070070514635621 56476482013138221494179)
                  ·
                    rfl

theorem cell21_247472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_247472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247472 prefixEnd_247472 := by exact prefixLift 247472
  have htrace : WordTrace (prefixWord ++ tailWord_247472) baseStart_247472 baseEnd_247472 := by
    simpa [prefixWord, tailWord_247472, baseEnd_247472] using wordTrace_append hprefix tailTrace_247472
  have hstable : (prefixWord ++ tailWord_247472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247472).length < 2 ^ (prefixWord ++ tailWord_247472).sum := by decide
  have hdescent : baseEnd_247472 < baseStart_247472 := by decide
  rcases family_descends (prefixWord ++ tailWord_247472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247523 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 4]
def baseStart_247523 : Nat := 118140960795 + 247523 * 2 ^ 59
def prefixEnd_247523 : Nat := 4983230072969 + 3 ^ 40 * 247523 * 2
def baseEnd_247523 : Nat := 56488120907973466144075

theorem tailTrace_247523 : CollatzResearch.WordTrace tailWord_247523 prefixEnd_247523 56488120907973466144075 := by
  unfold tailWord_247523
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027905482273919407939223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6018603654849279605292815 9027905482273919407939223)
  ·
    refine ⟨13541858223410879111908835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9027905482273919407939223 13541858223410879111908835)
    ·
      refine ⟨20312787335116318667863253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13541858223410879111908835 20312787335116318667863253)
      ·
        refine ⟨476080953166788718778045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20312787335116318667863253 476080953166788718778045)
        ·
          refine ⟨178530357437545769541767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476080953166788718778045 178530357437545769541767)
          ·
            refine ⟨267795536156318654312651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178530357437545769541767 267795536156318654312651)
            ·
              refine ⟨401693304234477981468977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267795536156318654312651 401693304234477981468977)
              ·
                refine ⟨301269978175858486101733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401693304234477981468977 301269978175858486101733)
                ·
                  refine ⟨56488120907973466144075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301269978175858486101733 56488120907973466144075)
                  ·
                    rfl

theorem cell21_247523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4].length) (baseStart_247523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247523 prefixEnd_247523 := by exact prefixLift 247523
  have htrace : WordTrace (prefixWord ++ tailWord_247523) baseStart_247523 baseEnd_247523 := by
    simpa [prefixWord, tailWord_247523, baseEnd_247523] using wordTrace_append hprefix tailTrace_247523
  have hstable : (prefixWord ++ tailWord_247523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247523).length < 2 ^ (prefixWord ++ tailWord_247523).sum := by decide
  have hdescent : baseEnd_247523 < baseStart_247523 := by decide
  rcases family_descends (prefixWord ++ tailWord_247523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247534 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_247534 : Nat := 118140960795 + 247534 * 2 ^ 59
def prefixEnd_247534 : Nat := 4983230072969 + 3 ^ 40 * 247534 * 2
def baseEnd_247534 : Nat := 56490631257839891460719

theorem tailTrace_247534 : CollatzResearch.WordTrace tailWord_247534 prefixEnd_247534 56490631257839891460719 := by
  unfold tailWord_247534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128538335654258535823707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6018871123489378857726437 1128538335654258535823707)
  ·
    refine ⟨1692807503481387803735561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128538335654258535823707 1692807503481387803735561)
    ·
      refine ⟨1269605627611040852801671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1692807503481387803735561 1269605627611040852801671)
      ·
        refine ⟨1904408441416561279202507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269605627611040852801671 1904408441416561279202507)
        ·
          refine ⟨2856612662124841918803761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904408441416561279202507 2856612662124841918803761)
          ·
            refine ⟨2142459496593631439102821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856612662124841918803761 2142459496593631439102821)
            ·
              refine ⟨401711155611305894831779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2142459496593631439102821 401711155611305894831779)
              ·
                refine ⟨602566733416958842247669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401711155611305894831779 602566733416958842247669)
                ·
                  refine ⟨56490631257839891460719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602566733416958842247669 56490631257839891460719)
                  ·
                    rfl

theorem cell21_247534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_247534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247534 prefixEnd_247534 := by exact prefixLift 247534
  have htrace : WordTrace (prefixWord ++ tailWord_247534) baseStart_247534 baseEnd_247534 := by
    simpa [prefixWord, tailWord_247534, baseEnd_247534] using wordTrace_append hprefix tailTrace_247534
  have hstable : (prefixWord ++ tailWord_247534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247534).length < 2 ^ (prefixWord ++ tailWord_247534).sum := by decide
  have hdescent : baseEnd_247534 < baseStart_247534 := by decide
  rcases family_descends (prefixWord ++ tailWord_247534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247540 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_247540 : Nat := 118140960795 + 247540 * 2 ^ 59
def prefixEnd_247540 : Nat := 4983230072969 + 3 ^ 40 * 247540 * 2
def baseEnd_247540 : Nat := 56492000539585214360707

theorem tailTrace_247540 : CollatzResearch.WordTrace tailWord_247540 prefixEnd_247540 56492000539585214360707 := by
  unfold tailWord_247540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514262761606165655654037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6019017015474887540872049 4514262761606165655654037)
  ·
    refine ⟨211606066950289015108783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4514262761606165655654037 211606066950289015108783)
    ·
      refine ⟨317409100425433522663175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211606066950289015108783 317409100425433522663175)
      ·
        refine ⟨476113650638150283994763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317409100425433522663175 476113650638150283994763)
        ·
          refine ⟨714170475957225425992145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476113650638150283994763 714170475957225425992145)
          ·
            refine ⟨535627856967919069494109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714170475957225425992145 535627856967919069494109)
            ·
              refine ⟨200860446362969651060291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535627856967919069494109 200860446362969651060291)
              ·
                refine ⟨301290669544454476590437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200860446362969651060291 301290669544454476590437)
                ·
                  refine ⟨56492000539585214360707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301290669544454476590437 56492000539585214360707)
                  ·
                    rfl

theorem cell21_247540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_247540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247540 prefixEnd_247540 := by exact prefixLift 247540
  have htrace : WordTrace (prefixWord ++ tailWord_247540) baseStart_247540 baseEnd_247540 := by
    simpa [prefixWord, tailWord_247540, baseEnd_247540] using wordTrace_append hprefix tailTrace_247540
  have hstable : (prefixWord ++ tailWord_247540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247540).length < 2 ^ (prefixWord ++ tailWord_247540).sum := by decide
  have hdescent : baseEnd_247540 < baseStart_247540 := by decide
  rcases family_descends (prefixWord ++ tailWord_247540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247607 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_247607 : Nat := 118140960795 + 247607 * 2 ^ 59
def prefixEnd_247607 : Nat := 4983230072969 + 3 ^ 40 * 247607 * 2
def baseEnd_247607 : Nat := 56507290852407986743903

theorem tailTrace_247607 : CollatzResearch.WordTrace tailWord_247607 prefixEnd_247607 56507290852407986743903 := by
  unfold tailWord_247607
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030969213969601753997075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6020646142646401169331383 9030969213969601753997075)
  ·
    refine ⟨13546453820954402630995613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030969213969601753997075 13546453820954402630995613)
    ·
      refine ⟨5079920182857900986623355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13546453820954402630995613 5079920182857900986623355)
      ·
        refine ⟨7619880274286851479935033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5079920182857900986623355 7619880274286851479935033)
        ·
          refine ⟨5714910205715138609951275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7619880274286851479935033 5714910205715138609951275)
          ·
            refine ⟨8572365308572707914926913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714910205715138609951275 8572365308572707914926913)
            ·
              refine ⟨6429273981429530936195185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572365308572707914926913 6429273981429530936195185)
              ·
                refine ⟨4821955486072148202146389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6429273981429530936195185 4821955486072148202146389)
                ·
                  refine ⟨56507290852407986743903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4821955486072148202146389 56507290852407986743903)
                  ·
                    rfl

theorem cell21_247607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_247607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247607 prefixEnd_247607 := by exact prefixLift 247607
  have htrace : WordTrace (prefixWord ++ tailWord_247607) baseStart_247607 baseEnd_247607 := by
    simpa [prefixWord, tailWord_247607, baseEnd_247607] using wordTrace_append hprefix tailTrace_247607
  have hstable : (prefixWord ++ tailWord_247607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247607).length < 2 ^ (prefixWord ++ tailWord_247607).sum := by decide
  have hdescent : baseEnd_247607 < baseStart_247607 := by decide
  rcases family_descends (prefixWord ++ tailWord_247607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247644 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_247644 : Nat := 118140960795 + 247644 * 2 ^ 59
def prefixEnd_247644 : Nat := 4983230072969 + 3 ^ 40 * 247644 * 2
def baseEnd_247644 : Nat := 56515734756504144627161

theorem tailTrace_247644 : CollatzResearch.WordTrace tailWord_247644 prefixEnd_247644 56515734756504144627161 := by
  unfold tailWord_247644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516159357417778536546993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6021545809890371382062657 4516159357417778536546993)
  ·
    refine ⟨3387119518063333902410245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4516159357417778536546993 3387119518063333902410245)
    ·
      refine ⟨635084909636875106701921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3387119518063333902410245 635084909636875106701921)
      ·
        refine ⟨476313682227656330026441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635084909636875106701921 476313682227656330026441)
        ·
          refine ⟨357235261670742247519831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476313682227656330026441 357235261670742247519831)
          ·
            refine ⟨535852892506113371279747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357235261670742247519831 535852892506113371279747)
            ·
              refine ⟨803779338759170056919621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535852892506113371279747 803779338759170056919621)
              ·
                refine ⟨150708626017344385672429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803779338759170056919621 150708626017344385672429)
                ·
                  refine ⟨56515734756504144627161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150708626017344385672429 56515734756504144627161)
                  ·
                    rfl

theorem cell21_247644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_247644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247644 prefixEnd_247644 := by exact prefixLift 247644
  have htrace : WordTrace (prefixWord ++ tailWord_247644) baseStart_247644 baseEnd_247644 := by
    simpa [prefixWord, tailWord_247644, baseEnd_247644] using wordTrace_append hprefix tailTrace_247644
  have hstable : (prefixWord ++ tailWord_247644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247644).length < 2 ^ (prefixWord ++ tailWord_247644).sum := by decide
  have hdescent : baseEnd_247644 < baseStart_247644 := by decide
  rcases family_descends (prefixWord ++ tailWord_247644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247759 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_247759 : Nat := 118140960795 + 247759 * 2 ^ 59
def prefixEnd_247759 : Nat := 4983230072969 + 3 ^ 40 * 247759 * 2
def baseEnd_247759 : Nat := 56541979323289500210259

theorem tailTrace_247759 : CollatzResearch.WordTrace tailWord_247759 prefixEnd_247759 56541979323289500210259 := by
  unfold tailWord_247759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036513109418931713530331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6024342072945954475686887 9036513109418931713530331)
  ·
    refine ⟨13554769664128397570295497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036513109418931713530331 13554769664128397570295497)
    ·
      refine ⟨10166077248096298177721623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13554769664128397570295497 10166077248096298177721623)
      ·
        refine ⟨15249115872144447266582435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166077248096298177721623 15249115872144447266582435)
        ·
          refine ⟨22873673808216670899873653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249115872144447266582435 22873673808216670899873653)
          ·
            refine ⟨2144406919520312896863155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22873673808216670899873653 2144406919520312896863155)
            ·
              refine ⟨3216610379280469345294733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144406919520312896863155 3216610379280469345294733)
              ·
                refine ⟨1206228892230176004485525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3216610379280469345294733 1206228892230176004485525)
                ·
                  refine ⟨56541979323289500210259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1206228892230176004485525 56541979323289500210259)
                  ·
                    rfl

theorem cell21_247759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_247759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247759 prefixEnd_247759 := by exact prefixLift 247759
  have htrace : WordTrace (prefixWord ++ tailWord_247759) baseStart_247759 baseEnd_247759 := by
    simpa [prefixWord, tailWord_247759, baseEnd_247759] using wordTrace_append hprefix tailTrace_247759
  have hstable : (prefixWord ++ tailWord_247759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247759).length < 2 ^ (prefixWord ++ tailWord_247759).sum := by decide
  have hdescent : baseEnd_247759 < baseStart_247759 := by decide
  rcases family_descends (prefixWord ++ tailWord_247759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247900 : List Nat := [2, 2, 4, 1, 1, 4, 2, 5]
def baseStart_247900 : Nat := 118140960795 + 247900 * 2 ^ 59
def prefixEnd_247900 : Nat := 4983230072969 + 3 ^ 40 * 247900 * 2
def baseEnd_247900 : Nat := 18858052481434862786657

theorem tailTrace_247900 : CollatzResearch.WordTrace tailWord_247900 prefixEnd_247900 18858052481434862786657 := by
  unfold tailWord_247900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520827900954056397206577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6027770534605408529608769 4520827900954056397206577)
  ·
    refine ⟨3390620925715542297904933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4520827900954056397206577 3390620925715542297904933)
    ·
      refine ⟨635741423571664180857175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3390620925715542297904933 635741423571664180857175)
      ·
        refine ⟨953612135357496271285763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635741423571664180857175 953612135357496271285763)
        ·
          refine ⟨1430418203036244406928645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953612135357496271285763 1430418203036244406928645)
          ·
            refine ⟨268203413069295826299121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1430418203036244406928645 268203413069295826299121)
            ·
              refine ⟨201152559801971869724341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268203413069295826299121 201152559801971869724341)
              ·
                refine ⟨18858052481434862786657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201152559801971869724341 18858052481434862786657)
                ·
                  rfl

theorem cell21_247900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_247900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247900 prefixEnd_247900 := by exact prefixLift 247900
  have htrace : WordTrace (prefixWord ++ tailWord_247900) baseStart_247900 baseEnd_247900 := by
    simpa [prefixWord, tailWord_247900, baseEnd_247900] using wordTrace_append hprefix tailTrace_247900
  have hstable : (prefixWord ++ tailWord_247900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247900).length < 2 ^ (prefixWord ++ tailWord_247900).sum := by decide
  have hdescent : baseEnd_247900 < baseStart_247900 := by decide
  rcases family_descends (prefixWord ++ tailWord_247900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247911 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_247911 : Nat := 118140960795 + 247911 * 2 ^ 59
def prefixEnd_247911 : Nat := 4983230072969 + 3 ^ 40 * 247911 * 2
def baseEnd_247911 : Nat := 56576667794171013676615

theorem tailTrace_247911 : CollatzResearch.WordTrace tailWord_247911 prefixEnd_247911 56576667794171013676615 := by
  unfold tailWord_247911
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042057004868261673063587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6028038003245507782042391 9042057004868261673063587)
  ·
    refine ⟨13563085507302392509595381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9042057004868261673063587 13563085507302392509595381)
    ·
      refine ⟨1271539266309599297774567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13563085507302392509595381 1271539266309599297774567)
      ·
        refine ⟨1907308899464398946661851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271539266309599297774567 1907308899464398946661851)
        ·
          refine ⟨2860963349196598419992777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907308899464398946661851 2860963349196598419992777)
          ·
            refine ⟨2145722511897448814994583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860963349196598419992777 2145722511897448814994583)
            ·
              refine ⟨3218583767846173222491875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145722511897448814994583 3218583767846173222491875)
              ·
                refine ⟨4827875651769259833737813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218583767846173222491875 4827875651769259833737813)
                ·
                  refine ⟨56576667794171013676615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4827875651769259833737813 56576667794171013676615)
                  ·
                    rfl

theorem cell21_247911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_247911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247911 prefixEnd_247911 := by exact prefixLift 247911
  have htrace : WordTrace (prefixWord ++ tailWord_247911) baseStart_247911 baseEnd_247911 := by
    simpa [prefixWord, tailWord_247911, baseEnd_247911] using wordTrace_append hprefix tailTrace_247911
  have hstable : (prefixWord ++ tailWord_247911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247911).length < 2 ^ (prefixWord ++ tailWord_247911).sum := by decide
  have hdescent : baseEnd_247911 < baseStart_247911 := by decide
  rcases family_descends (prefixWord ++ tailWord_247911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247982 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_247982 : Nat := 118140960795 + 247982 * 2 ^ 59
def prefixEnd_247982 : Nat := 4983230072969 + 3 ^ 40 * 247982 * 2
def baseEnd_247982 : Nat := 56592870961490667993137

theorem tailTrace_247982 : CollatzResearch.WordTrace tailWord_247982 prefixEnd_247982 56592870961490667993137 := by
  unfold tailWord_247982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130580823451380099862275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6029764391740693865932133 1130580823451380099862275)
  ·
    refine ⟨1695871235177070149793413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1130580823451380099862275 1695871235177070149793413)
    ·
      refine ⟨317975856595700653086265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1695871235177070149793413 317975856595700653086265)
      ·
        refine ⟨238481892446775489814699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317975856595700653086265 238481892446775489814699)
        ·
          refine ⟨357722838670163234722049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238481892446775489814699 357722838670163234722049)
          ·
            refine ⟨268292129002622426041537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357722838670163234722049 268292129002622426041537)
            ·
              refine ⟨201219096751966819531153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268292129002622426041537 201219096751966819531153)
              ·
                refine ⟨150914322563975114648365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201219096751966819531153 150914322563975114648365)
                ·
                  refine ⟨56592870961490667993137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150914322563975114648365 56592870961490667993137)
                  ·
                    rfl

theorem cell21_247982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_247982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_247982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_247982 prefixEnd_247982 := by exact prefixLift 247982
  have htrace : WordTrace (prefixWord ++ tailWord_247982) baseStart_247982 baseEnd_247982 := by
    simpa [prefixWord, tailWord_247982, baseEnd_247982] using wordTrace_append hprefix tailTrace_247982
  have hstable : (prefixWord ++ tailWord_247982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247982).length < 2 ^ (prefixWord ++ tailWord_247982).sum := by decide
  have hdescent : baseEnd_247982 < baseStart_247982 := by decide
  rcases family_descends (prefixWord ++ tailWord_247982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248032 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_248032 : Nat := 118140960795 + 248032 * 2 ^ 59
def prefixEnd_248032 : Nat := 4983230072969 + 3 ^ 40 * 248032 * 2
def baseEnd_248032 : Nat := 56604281642701692159701

theorem tailTrace_248032 : CollatzResearch.WordTrace tailWord_248032 prefixEnd_248032 56604281642701692159701 := by
  unfold tailWord_248032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523235118714949669109175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6030980158286599558812233 4523235118714949669109175)
  ·
    refine ⟨6784852678072424503663763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523235118714949669109175 6784852678072424503663763)
    ·
      refine ⟨10177279017108636755495645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6784852678072424503663763 10177279017108636755495645)
      ·
        refine ⟨3816479631415738783310867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10177279017108636755495645 3816479631415738783310867)
        ·
          refine ⟨5724719447123608174966301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816479631415738783310867 5724719447123608174966301)
          ·
            refine ⟨2146769792671353065612363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5724719447123608174966301 2146769792671353065612363)
            ·
              refine ⟨3220154689007029598418545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146769792671353065612363 3220154689007029598418545)
              ·
                refine ⟨2415116016755272198813909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220154689007029598418545 2415116016755272198813909)
                ·
                  refine ⟨56604281642701692159701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2415116016755272198813909 56604281642701692159701)
                  ·
                    rfl

theorem cell21_248032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_248032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248032 prefixEnd_248032 := by exact prefixLift 248032
  have htrace : WordTrace (prefixWord ++ tailWord_248032) baseStart_248032 baseEnd_248032 := by
    simpa [prefixWord, tailWord_248032, baseEnd_248032] using wordTrace_append hprefix tailTrace_248032
  have hstable : (prefixWord ++ tailWord_248032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248032).length < 2 ^ (prefixWord ++ tailWord_248032).sum := by decide
  have hdescent : baseEnd_248032 < baseStart_248032 := by decide
  rcases family_descends (prefixWord ++ tailWord_248032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248035 : List Nat := [1, 1, 1, 8, 1, 1, 8]
def baseStart_248035 : Nat := 118140960795 + 248035 * 2 ^ 59
def prefixEnd_248035 : Nat := 4983230072969 + 3 ^ 40 * 248035 * 2
def baseEnd_248035 : Nat := 6289440698174928178855

theorem tailTrace_248035 : CollatzResearch.WordTrace tailWord_248035 prefixEnd_248035 6289440698174928178855 := by
  unfold tailWord_248035
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046579656419030850577559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6031053104279353900385039 9046579656419030850577559)
  ·
    refine ⟨13569869484628546275866339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046579656419030850577559 13569869484628546275866339)
    ·
      refine ⟨20354804226942819413799509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569869484628546275866339 20354804226942819413799509)
      ·
        refine ⟨238532862034486165005463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 20354804226942819413799509 238532862034486165005463)
        ·
          refine ⟨357799293051729247508195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238532862034486165005463 357799293051729247508195)
          ·
            refine ⟨536698939577593871262293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357799293051729247508195 536698939577593871262293)
            ·
              refine ⟨6289440698174928178855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 536698939577593871262293 6289440698174928178855)
              ·
                rfl

theorem cell21_248035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 8].length) (baseStart_248035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248035 prefixEnd_248035 := by exact prefixLift 248035
  have htrace : WordTrace (prefixWord ++ tailWord_248035) baseStart_248035 baseEnd_248035 := by
    simpa [prefixWord, tailWord_248035, baseEnd_248035] using wordTrace_append hprefix tailTrace_248035
  have hstable : (prefixWord ++ tailWord_248035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248035).length < 2 ^ (prefixWord ++ tailWord_248035).sum := by decide
  have hdescent : baseEnd_248035 < baseStart_248035 := by decide
  rcases family_descends (prefixWord ++ tailWord_248035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248066 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_248066 : Nat := 118140960795 + 248066 * 2 ^ 59
def prefixEnd_248066 : Nat := 4983230072969 + 3 ^ 40 * 248066 * 2
def baseEnd_248066 : Nat := 56612040905925188592965

theorem tailTrace_248066 : CollatzResearch.WordTrace tailWord_248066 prefixEnd_248066 56612040905925188592965 := by
  unfold tailWord_248066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261927579826680786239013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6031806879537815429970701 2261927579826680786239013)
  ·
    refine ⟨424111421217502647419815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2261927579826680786239013 424111421217502647419815)
    ·
      refine ⟨636167131826253971129723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424111421217502647419815 636167131826253971129723)
      ·
        refine ⟨954250697739380956694585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636167131826253971129723 954250697739380956694585)
        ·
          refine ⟨715688023304535717520939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954250697739380956694585 715688023304535717520939)
          ·
            refine ⟨1073532034956803576281409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715688023304535717520939 1073532034956803576281409)
            ·
              refine ⟨805149026217602682211057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073532034956803576281409 805149026217602682211057)
              ·
                refine ⟨603861769663202011658293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805149026217602682211057 603861769663202011658293)
                ·
                  refine ⟨56612040905925188592965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 603861769663202011658293 56612040905925188592965)
                  ·
                    rfl

theorem cell21_248066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_248066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248066 prefixEnd_248066 := by exact prefixLift 248066
  have htrace : WordTrace (prefixWord ++ tailWord_248066) baseStart_248066 baseEnd_248066 := by
    simpa [prefixWord, tailWord_248066, baseEnd_248066] using wordTrace_append hprefix tailTrace_248066
  have hstable : (prefixWord ++ tailWord_248066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248066).length < 2 ^ (prefixWord ++ tailWord_248066).sum := by decide
  have hdescent : baseEnd_248066 < baseStart_248066 := by decide
  rcases family_descends (prefixWord ++ tailWord_248066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248114 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_248114 : Nat := 118140960795 + 248114 * 2 ^ 59
def prefixEnd_248114 : Nat := 4983230072969 + 3 ^ 40 * 248114 * 2
def baseEnd_248114 : Nat := 56622995159887771792867

theorem tailTrace_248114 : CollatzResearch.WordTrace tailWord_248114 prefixEnd_248114 56622995159887771792867 := by
  unfold tailWord_248114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262365255783206835675849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6032974015421884895135597 2262365255783206835675849)
  ·
    refine ⟨1696773941837405126756887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2262365255783206835675849 1696773941837405126756887)
    ·
      refine ⟨2545160912756107690135331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696773941837405126756887 2545160912756107690135331)
      ·
        refine ⟨3817741369134161535202997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545160912756107690135331 3817741369134161535202997)
        ·
          refine ⟨357913253356327643925281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3817741369134161535202997 357913253356327643925281)
          ·
            refine ⟨268434940017245732943961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357913253356327643925281 268434940017245732943961)
            ·
              refine ⟨201326205012934299707971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268434940017245732943961 201326205012934299707971)
              ·
                refine ⟨301989307519401449561957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201326205012934299707971 301989307519401449561957)
                ·
                  refine ⟨56622995159887771792867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301989307519401449561957 56622995159887771792867)
                  ·
                    rfl

theorem cell21_248114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_248114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248114 prefixEnd_248114 := by exact prefixLift 248114
  have htrace : WordTrace (prefixWord ++ tailWord_248114) baseStart_248114 baseEnd_248114 := by
    simpa [prefixWord, tailWord_248114, baseEnd_248114] using wordTrace_append hprefix tailTrace_248114
  have hstable : (prefixWord ++ tailWord_248114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248114).length < 2 ^ (prefixWord ++ tailWord_248114).sum := by decide
  have hdescent : baseEnd_248114 < baseStart_248114 := by decide
  rcases family_descends (prefixWord ++ tailWord_248114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248218 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_248218 : Nat := 118140960795 + 248218 * 2 ^ 59
def prefixEnd_248218 : Nat := 4983230072969 + 3 ^ 40 * 248218 * 2
def baseEnd_248218 : Nat := 56646729376806702059321

theorem tailTrace_248218 : CollatzResearch.WordTrace tailWord_248218 prefixEnd_248218 56646729376806702059321 := by
  unfold tailWord_248218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263313553689013276122327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6035502809837368736326205 2263313553689013276122327)
  ·
    refine ⟨3394970330533519914183491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263313553689013276122327 3394970330533519914183491)
    ·
      refine ⟨5092455495800279871275237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394970330533519914183491 5092455495800279871275237)
      ·
        refine ⟨954835405462552475864107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5092455495800279871275237 954835405462552475864107)
        ·
          refine ⟨1432253108193828713796161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954835405462552475864107 1432253108193828713796161)
          ·
            refine ⟨1074189831145371535347121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432253108193828713796161 1074189831145371535347121)
            ·
              refine ⟨805642373359028651510341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074189831145371535347121 805642373359028651510341)
              ·
                refine ⟨151057945004817872158189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805642373359028651510341 151057945004817872158189)
                ·
                  refine ⟨56646729376806702059321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151057945004817872158189 56646729376806702059321)
                  ·
                    rfl

theorem cell21_248218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_248218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248218 prefixEnd_248218 := by exact prefixLift 248218
  have htrace : WordTrace (prefixWord ++ tailWord_248218) baseStart_248218 baseEnd_248218 := by
    simpa [prefixWord, tailWord_248218, baseEnd_248218] using wordTrace_append hprefix tailTrace_248218
  have hstable : (prefixWord ++ tailWord_248218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248218).length < 2 ^ (prefixWord ++ tailWord_248218).sum := by decide
  have hdescent : baseEnd_248218 < baseStart_248218 := by decide
  rcases family_descends (prefixWord ++ tailWord_248218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248229 : List Nat := [1, 3, 1, 2, 1, 1, 4, 8]
def baseStart_248229 : Nat := 118140960795 + 248229 * 2 ^ 59
def prefixEnd_248229 : Nat := 4983230072969 + 3 ^ 40 * 248229 * 2
def baseEnd_248229 : Nat := 18883079908891042458655

theorem tailTrace_248229 : CollatzResearch.WordTrace tailWord_248229 prefixEnd_248229 18883079908891042458655 := by
  unfold tailWord_248229
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053655417716201983139741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6035770278477467988759827 9053655417716201983139741)
  ·
    refine ⟨3395120781643575743677403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9053655417716201983139741 3395120781643575743677403)
    ·
      refine ⟨5092681172465363615516105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395120781643575743677403 5092681172465363615516105)
      ·
        refine ⟨3819510879349022711637079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092681172465363615516105 3819510879349022711637079)
        ·
          refine ⟨5729266319023534067455619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819510879349022711637079 5729266319023534067455619)
          ·
            refine ⟨8593899478535301101183429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729266319023534067455619 8593899478535301101183429)
            ·
              refine ⟨1611356152225368956471893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8593899478535301101183429 1611356152225368956471893)
              ·
                refine ⟨18883079908891042458655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1611356152225368956471893 18883079908891042458655)
                ·
                  rfl

theorem cell21_248229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_248229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248229 prefixEnd_248229 := by exact prefixLift 248229
  have htrace : WordTrace (prefixWord ++ tailWord_248229) baseStart_248229 baseEnd_248229 := by
    simpa [prefixWord, tailWord_248229, baseEnd_248229] using wordTrace_append hprefix tailTrace_248229
  have hstable : (prefixWord ++ tailWord_248229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248229).length < 2 ^ (prefixWord ++ tailWord_248229).sum := by decide
  have hdescent : baseEnd_248229 < baseStart_248229 := by decide
  rcases family_descends (prefixWord ++ tailWord_248229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248277 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_248277 : Nat := 118140960795 + 248277 * 2 ^ 59
def prefixEnd_248277 : Nat := 4983230072969 + 3 ^ 40 * 248277 * 2
def baseEnd_248277 : Nat := 56660193980635710575867

theorem tailTrace_248277 : CollatzResearch.WordTrace tailWord_248277 prefixEnd_248277 56660193980635710575867 := by
  unfold tailWord_248277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055406121542306180887085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6036937414361537453924723 9055406121542306180887085)
  ·
    refine ⟨3395777295578364817832657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9055406121542306180887085 3395777295578364817832657)
    ·
      refine ⟨2546832971683773613374493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395777295578364817832657 2546832971683773613374493)
      ·
        refine ⟨955062364381415105015435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2546832971683773613374493 955062364381415105015435)
        ·
          refine ⟨1432593546572122657523153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955062364381415105015435 1432593546572122657523153)
          ·
            refine ⟨1074445159929091993142365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432593546572122657523153 1074445159929091993142365)
            ·
              refine ⟨402916934973409497428387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1074445159929091993142365 402916934973409497428387)
              ·
                refine ⟨604375402460114246142581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402916934973409497428387 604375402460114246142581)
                ·
                  refine ⟨56660193980635710575867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 604375402460114246142581 56660193980635710575867)
                  ·
                    rfl

theorem cell21_248277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_248277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248277 prefixEnd_248277 := by exact prefixLift 248277
  have htrace : WordTrace (prefixWord ++ tailWord_248277) baseStart_248277 baseEnd_248277 := by
    simpa [prefixWord, tailWord_248277, baseEnd_248277] using wordTrace_append hprefix tailTrace_248277
  have hstable : (prefixWord ++ tailWord_248277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248277).length < 2 ^ (prefixWord ++ tailWord_248277).sum := by decide
  have hdescent : baseEnd_248277 < baseStart_248277 := by decide
  rcases family_descends (prefixWord ++ tailWord_248277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248305 : List Nat := [1, 2, 2, 2, 3, 1, 1, 9]
def baseStart_248305 : Nat := 118140960795 + 248305 * 2 ^ 59
def prefixEnd_248305 : Nat := 4983230072969 + 3 ^ 40 * 248305 * 2
def baseEnd_248305 : Nat := 18888861320704628036381

theorem tailTrace_248305 : CollatzResearch.WordTrace tailWord_248305 prefixEnd_248305 18888861320704628036381 := by
  unfold tailWord_248305
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056427365440866962906369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6037618243627244641937579 9056427365440866962906369)
  ·
    refine ⟨6792320524080650222179777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9056427365440866962906369 6792320524080650222179777)
    ·
      refine ⟨5094240393060487666634833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6792320524080650222179777 5094240393060487666634833)
      ·
        refine ⟨3820680294795365749976125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5094240393060487666634833 3820680294795365749976125)
        ·
          refine ⟨1432755110548262156241047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3820680294795365749976125 1432755110548262156241047)
          ·
            refine ⟨2149132665822393234361571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432755110548262156241047 2149132665822393234361571)
            ·
              refine ⟨3223698998733589851542357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149132665822393234361571 3223698998733589851542357)
              ·
                refine ⟨18888861320704628036381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3223698998733589851542357 18888861320704628036381)
                ·
                  rfl

theorem cell21_248305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_248305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248305 prefixEnd_248305 := by exact prefixLift 248305
  have htrace : WordTrace (prefixWord ++ tailWord_248305) baseStart_248305 baseEnd_248305 := by
    simpa [prefixWord, tailWord_248305, baseEnd_248305] using wordTrace_append hprefix tailTrace_248305
  have hstable : (prefixWord ++ tailWord_248305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248305).length < 2 ^ (prefixWord ++ tailWord_248305).sum := by decide
  have hdescent : baseEnd_248305 < baseStart_248305 := by decide
  rcases family_descends (prefixWord ++ tailWord_248305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248322 : List Nat := [3, 4, 1, 2, 11]
def baseStart_248322 : Nat := 118140960795 + 248322 * 2 ^ 59
def prefixEnd_248322 : Nat := 4983230072969 + 3 ^ 40 * 248322 * 2
def baseEnd_248322 : Nat := 699635353008958423775

theorem tailTrace_248322 : CollatzResearch.WordTrace tailWord_248322 prefixEnd_248322 699635353008958423775 := by
  unfold tailWord_248322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264261851594819716568805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6038031604252852577516813 2264261851594819716568805)
  ·
    refine ⟨424549097174028696856651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2264261851594819716568805 424549097174028696856651)
    ·
      refine ⟨636823645761043045284977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424549097174028696856651 636823645761043045284977)
      ·
        refine ⟨477617734320782283963733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636823645761043045284977 477617734320782283963733)
        ·
          refine ⟨699635353008958423775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 477617734320782283963733 699635353008958423775)
          ·
            rfl

theorem cell21_248322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 11].length) (baseStart_248322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248322 prefixEnd_248322 := by exact prefixLift 248322
  have htrace : WordTrace (prefixWord ++ tailWord_248322) baseStart_248322 baseEnd_248322 := by
    simpa [prefixWord, tailWord_248322, baseEnd_248322] using wordTrace_append hprefix tailTrace_248322
  have hstable : (prefixWord ++ tailWord_248322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248322).length < 2 ^ (prefixWord ++ tailWord_248322).sum := by decide
  have hdescent : baseEnd_248322 < baseStart_248322 := by decide
  rcases family_descends (prefixWord ++ tailWord_248322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248356 : List Nat := [2, 3, 1, 5, 1, 1, 3, 5]
def baseStart_248356 : Nat := 118140960795 + 248356 * 2 ^ 59
def prefixEnd_248356 : Nat := 4983230072969 + 3 ^ 40 * 248356 * 2
def baseEnd_248356 : Nat := 18892740952316376253013

theorem tailTrace_248356 : CollatzResearch.WordTrace tailWord_248356 prefixEnd_248356 18892740952316376253013 := by
  unfold tailWord_248356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529143744128051336506461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6038858325504068448675281 4529143744128051336506461)
  ·
    refine ⟨1698428904048019251189923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4529143744128051336506461 1698428904048019251189923)
    ·
      refine ⟨2547643356072028876784885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698428904048019251189923 2547643356072028876784885)
      ·
        refine ⟨238841564631752707198583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2547643356072028876784885 238841564631752707198583)
        ·
          refine ⟨358262346947629060797875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238841564631752707198583 358262346947629060797875)
          ·
            refine ⟨537393520421443591196813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358262346947629060797875 537393520421443591196813)
            ·
              refine ⟨201522570158041346698805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537393520421443591196813 201522570158041346698805)
              ·
                refine ⟨18892740952316376253013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201522570158041346698805 18892740952316376253013)
                ·
                  rfl

theorem cell21_248356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_248356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248356 prefixEnd_248356 := by exact prefixLift 248356
  have htrace : WordTrace (prefixWord ++ tailWord_248356) baseStart_248356 baseEnd_248356 := by
    simpa [prefixWord, tailWord_248356, baseEnd_248356] using wordTrace_append hprefix tailTrace_248356
  have hstable : (prefixWord ++ tailWord_248356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248356).length < 2 ^ (prefixWord ++ tailWord_248356).sum := by decide
  have hdescent : baseEnd_248356 < baseStart_248356 := by decide
  rcases family_descends (prefixWord ++ tailWord_248356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248497 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 3]
def baseStart_248497 : Nat := 118140960795 + 248497 * 2 ^ 59
def prefixEnd_248497 : Nat := 4983230072969 + 3 ^ 40 * 248497 * 2
def baseEnd_248497 : Nat := 56710400977964216908751

theorem tailTrace_248497 : CollatzResearch.WordTrace tailWord_248497 prefixEnd_248497 56710400977964216908751 := by
  unfold tailWord_248497
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063430180745283753895745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6042286787163522502597163 9063430180745283753895745)
  ·
    refine ⟨6797572635558962815421809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9063430180745283753895745 6797572635558962815421809)
    ·
      refine ⟨5098179476669222111566357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6797572635558962815421809 5098179476669222111566357)
      ·
        refine ⟨238977162968869786479673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5098179476669222111566357 238977162968869786479673)
        ·
          refine ⟨179232872226652339859755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238977162968869786479673 179232872226652339859755)
          ·
            refine ⟨268849308339978509789633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179232872226652339859755 268849308339978509789633)
            ·
              refine ⟨201636981254983882342225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268849308339978509789633 201636981254983882342225)
              ·
                refine ⟨151227735941237911756669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201636981254983882342225 151227735941237911756669)
                ·
                  refine ⟨56710400977964216908751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151227735941237911756669 56710400977964216908751)
                  ·
                    rfl

theorem cell21_248497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_248497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248497 prefixEnd_248497 := by exact prefixLift 248497
  have htrace : WordTrace (prefixWord ++ tailWord_248497) baseStart_248497 baseEnd_248497 := by
    simpa [prefixWord, tailWord_248497, baseEnd_248497] using wordTrace_append hprefix tailTrace_248497
  have hstable : (prefixWord ++ tailWord_248497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248497).length < 2 ^ (prefixWord ++ tailWord_248497).sum := by decide
  have hdescent : baseEnd_248497 < baseStart_248497 := by decide
  rcases family_descends (prefixWord ++ tailWord_248497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248629 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 4]
def baseStart_248629 : Nat := 118140960795 + 248629 * 2 ^ 59
def prefixEnd_248629 : Nat := 4983230072969 + 3 ^ 40 * 248629 * 2
def baseEnd_248629 : Nat := 56740525176361320708481

theorem tailTrace_248629 : CollatzResearch.WordTrace tailWord_248629 prefixEnd_248629 56740525176361320708481 := by
  unfold tailWord_248629
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068244616267070297700941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6045496410844713531800627 9068244616267070297700941)
  ·
    refine ⟨3400591731100151361637853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9068244616267070297700941 3400591731100151361637853)
    ·
      refine ⟨1275221899162556760614195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3400591731100151361637853 1275221899162556760614195)
      ·
        refine ⟨1912832848743835140921293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275221899162556760614195 1912832848743835140921293)
        ·
          refine ⟨717312318278938177845485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1912832848743835140921293 717312318278938177845485)
          ·
            refine ⟨268992119354601816692057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717312318278938177845485 268992119354601816692057)
            ·
              refine ⟨201744089515951362519043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268992119354601816692057 201744089515951362519043)
              ·
                refine ⟨302616134273927043778565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201744089515951362519043 302616134273927043778565)
                ·
                  refine ⟨56740525176361320708481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302616134273927043778565 56740525176361320708481)
                  ·
                    rfl

theorem cell21_248629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_248629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248629 prefixEnd_248629 := by exact prefixLift 248629
  have htrace : WordTrace (prefixWord ++ tailWord_248629) baseStart_248629 baseEnd_248629 := by
    simpa [prefixWord, tailWord_248629, baseEnd_248629] using wordTrace_append hprefix tailTrace_248629
  have hstable : (prefixWord ++ tailWord_248629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248629).length < 2 ^ (prefixWord ++ tailWord_248629).sum := by decide
  have hdescent : baseEnd_248629 < baseStart_248629 := by decide
  rcases family_descends (prefixWord ++ tailWord_248629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248654 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_248654 : Nat := 118140960795 + 248654 * 2 ^ 59
def prefixEnd_248654 : Nat := 4983230072969 + 3 ^ 40 * 248654 * 2
def baseEnd_248654 : Nat := 56746230516966832791763

theorem tailTrace_248654 : CollatzResearch.WordTrace tailWord_248654 prefixEnd_248654 56746230516966832791763 := by
  unfold tailWord_248654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133644555147062445920127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6046104294117666378240677 1133644555147062445920127)
  ·
    refine ⟨1700466832720593668880191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133644555147062445920127 1700466832720593668880191)
    ·
      refine ⟨2550700249080890503320287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700466832720593668880191 2550700249080890503320287)
      ·
        refine ⟨3826050373621335754980431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550700249080890503320287 3826050373621335754980431)
        ·
          refine ⟨5739075560432003632470647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826050373621335754980431 5739075560432003632470647)
          ·
            refine ⟨8608613340648005448705971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739075560432003632470647 8608613340648005448705971)
            ·
              refine ⟨12912920010972008173058957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608613340648005448705971 12912920010972008173058957)
              ·
                refine ⟨4842345004114503064897109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12912920010972008173058957 4842345004114503064897109)
                ·
                  refine ⟨56746230516966832791763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4842345004114503064897109 56746230516966832791763)
                  ·
                    rfl

theorem cell21_248654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_248654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248654 prefixEnd_248654 := by exact prefixLift 248654
  have htrace : WordTrace (prefixWord ++ tailWord_248654) baseStart_248654 baseEnd_248654 := by
    simpa [prefixWord, tailWord_248654, baseEnd_248654] using wordTrace_append hprefix tailTrace_248654
  have hstable : (prefixWord ++ tailWord_248654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248654).length < 2 ^ (prefixWord ++ tailWord_248654).sum := by decide
  have hdescent : baseEnd_248654 < baseStart_248654 := by decide
  rcases family_descends (prefixWord ++ tailWord_248654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248671 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_248671 : Nat := 118140960795 + 248671 * 2 ^ 59
def prefixEnd_248671 : Nat := 4983230072969 + 3 ^ 40 * 248671 * 2
def baseEnd_248671 : Nat := 56750110148578581008395

theorem tailTrace_248671 : CollatzResearch.WordTrace tailWord_248671 prefixEnd_248671 56750110148578581008395 := by
  unfold tailWord_248671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069776482114911470729867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6046517654743274313819911 9069776482114911470729867)
  ·
    refine ⟨13604664723172367206094801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069776482114911470729867 13604664723172367206094801)
    ·
      refine ⟨10203498542379275404571101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13604664723172367206094801 10203498542379275404571101)
      ·
        refine ⟨3826311953392228276714163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10203498542379275404571101 3826311953392228276714163)
        ·
          refine ⟨5739467930088342415071245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826311953392228276714163 5739467930088342415071245)
          ·
            refine ⟨2152300473783128405651717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5739467930088342415071245 2152300473783128405651717)
            ·
              refine ⟨403556338834336576059697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2152300473783128405651717 403556338834336576059697)
              ·
                refine ⟨302667254125752432044773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403556338834336576059697 302667254125752432044773)
                ·
                  refine ⟨56750110148578581008395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302667254125752432044773 56750110148578581008395)
                  ·
                    rfl

theorem cell21_248671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_248671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248671 prefixEnd_248671 := by exact prefixLift 248671
  have htrace : WordTrace (prefixWord ++ tailWord_248671) baseStart_248671 baseEnd_248671 := by
    simpa [prefixWord, tailWord_248671, baseEnd_248671] using wordTrace_append hprefix tailTrace_248671
  have hstable : (prefixWord ++ tailWord_248671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248671).length < 2 ^ (prefixWord ++ tailWord_248671).sum := by decide
  have hdescent : baseEnd_248671 < baseStart_248671 := by decide
  rcases family_descends (prefixWord ++ tailWord_248671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248699 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_248699 : Nat := 118140960795 + 248699 * 2 ^ 59
def prefixEnd_248699 : Nat := 4983230072969 + 3 ^ 40 * 248699 * 2
def baseEnd_248699 : Nat := 56756500130056754541671

theorem tailTrace_248699 : CollatzResearch.WordTrace tailWord_248699 prefixEnd_248699 56756500130056754541671 := by
  unfold tailWord_248699
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070797726013472252749151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6047198484008981501832767 9070797726013472252749151)
  ·
    refine ⟨13606196589020208379123727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9070797726013472252749151 13606196589020208379123727)
    ·
      refine ⟨20409294883530312568685591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606196589020208379123727 20409294883530312568685591)
      ·
        refine ⟨30613942325295468853028387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409294883530312568685591 30613942325295468853028387)
        ·
          refine ⟨45920913487943203279542581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30613942325295468853028387 45920913487943203279542581)
          ·
            refine ⟨4305085639494675307457117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45920913487943203279542581 4305085639494675307457117)
            ·
              refine ⟨1614407114810503240296419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4305085639494675307457117 1614407114810503240296419)
              ·
                refine ⟨2421610672215754860444629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614407114810503240296419 2421610672215754860444629)
                ·
                  refine ⟨56756500130056754541671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2421610672215754860444629 56756500130056754541671)
                  ·
                    rfl

theorem cell21_248699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_248699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248699 prefixEnd_248699 := by exact prefixLift 248699
  have htrace : WordTrace (prefixWord ++ tailWord_248699) baseStart_248699 baseEnd_248699 := by
    simpa [prefixWord, tailWord_248699, baseEnd_248699] using wordTrace_append hprefix tailTrace_248699
  have hstable : (prefixWord ++ tailWord_248699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248699).length < 2 ^ (prefixWord ++ tailWord_248699).sum := by decide
  have hdescent : baseEnd_248699 < baseStart_248699 := by decide
  rcases family_descends (prefixWord ++ tailWord_248699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248722 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_248722 : Nat := 118140960795 + 248722 * 2 ^ 59
def prefixEnd_248722 : Nat := 4983230072969 + 3 ^ 40 * 248722 * 2
def baseEnd_248722 : Nat := 56761749043413825658291

theorem tailTrace_248722 : CollatzResearch.WordTrace tailWord_248722 prefixEnd_248722 56761749043413825658291 := by
  unfold tailWord_248722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267909151232536795209105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6047757736620098120557613 2267909151232536795209105)
  ·
    refine ⟨1700931863424402596406829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2267909151232536795209105 1700931863424402596406829)
    ·
      refine ⟨637849448784150973652561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1700931863424402596406829 637849448784150973652561)
      ·
        refine ⟨478387086588113230239421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637849448784150973652561 478387086588113230239421)
        ·
          refine ⟨179395157470542461339783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478387086588113230239421 179395157470542461339783)
          ·
            refine ⟨269092736205813692009675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179395157470542461339783 269092736205813692009675)
            ·
              refine ⟨403639104308720538014513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269092736205813692009675 403639104308720538014513)
              ·
                refine ⟨302729328231540403510885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403639104308720538014513 302729328231540403510885)
                ·
                  refine ⟨56761749043413825658291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302729328231540403510885 56761749043413825658291)
                  ·
                    rfl

theorem cell21_248722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_248722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248722 prefixEnd_248722 := by exact prefixLift 248722
  have htrace : WordTrace (prefixWord ++ tailWord_248722) baseStart_248722 baseEnd_248722 := by
    simpa [prefixWord, tailWord_248722, baseEnd_248722] using wordTrace_append hprefix tailTrace_248722
  have hstable : (prefixWord ++ tailWord_248722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248722).length < 2 ^ (prefixWord ++ tailWord_248722).sum := by decide
  have hdescent : baseEnd_248722 < baseStart_248722 := by decide
  rcases family_descends (prefixWord ++ tailWord_248722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248733 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 3]
def baseStart_248733 : Nat := 118140960795 + 248733 * 2 ^ 59
def prefixEnd_248733 : Nat := 4983230072969 + 3 ^ 40 * 248733 * 2
def baseEnd_248733 : Nat := 56764259393280250974935

theorem tailTrace_248733 : CollatzResearch.WordTrace tailWord_248733 prefixEnd_248733 56764259393280250974935 := by
  unfold tailWord_248733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9072037807890296059486853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6048025205260197372991235 9072037807890296059486853)
  ·
    refine ⟨1701007088979430511153785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9072037807890296059486853 1701007088979430511153785)
    ·
      refine ⟨1275755316734572883365339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1701007088979430511153785 1275755316734572883365339)
      ·
        refine ⟨1913632975101859325048009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275755316734572883365339 1913632975101859325048009)
        ·
          refine ⟨1435224731326394493786007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1913632975101859325048009 1435224731326394493786007)
          ·
            refine ⟨2152837096989591740679011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435224731326394493786007 2152837096989591740679011)
            ·
              refine ⟨3229255645484387611018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152837096989591740679011 3229255645484387611018517)
              ·
                refine ⟨151371358382080669266493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3229255645484387611018517 151371358382080669266493)
                ·
                  refine ⟨56764259393280250974935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151371358382080669266493 56764259393280250974935)
                  ·
                    rfl

theorem cell21_248733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_248733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248733 prefixEnd_248733 := by exact prefixLift 248733
  have htrace : WordTrace (prefixWord ++ tailWord_248733) baseStart_248733 baseEnd_248733 := by
    simpa [prefixWord, tailWord_248733, baseEnd_248733] using wordTrace_append hprefix tailTrace_248733
  have hstable : (prefixWord ++ tailWord_248733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248733).length < 2 ^ (prefixWord ++ tailWord_248733).sum := by decide
  have hdescent : baseEnd_248733 < baseStart_248733 := by decide
  rcases family_descends (prefixWord ++ tailWord_248733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248761 : List Nat := [1, 2, 1, 4, 2, 3, 1, 7]
def baseStart_248761 : Nat := 118140960795 + 248761 * 2 ^ 59
def prefixEnd_248761 : Nat := 4983230072969 + 3 ^ 40 * 248761 * 2
def baseEnd_248761 : Nat := 18923549791586141502737

theorem tailTrace_248761 : CollatzResearch.WordTrace tailWord_248761 prefixEnd_248761 18923549791586141502737 := by
  unfold tailWord_248761
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073059051788856841506137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6048706034525904561004091 9073059051788856841506137)
  ·
    refine ⟨6804794288841642631129603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9073059051788856841506137 6804794288841642631129603)
    ·
      refine ⟨10207191433262463946694405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804794288841642631129603 10207191433262463946694405)
      ·
        refine ⟨1913848393736711990005201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10207191433262463946694405 1913848393736711990005201)
        ·
          refine ⟨1435386295302533992503901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1913848393736711990005201 1435386295302533992503901)
          ·
            refine ⟨538269860738450247188963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1435386295302533992503901 538269860738450247188963)
            ·
              refine ⟨807404791107675370783445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538269860738450247188963 807404791107675370783445)
              ·
                refine ⟨18923549791586141502737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 807404791107675370783445 18923549791586141502737)
                ·
                  rfl

theorem cell21_248761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_248761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248761 prefixEnd_248761 := by exact prefixLift 248761
  have htrace : WordTrace (prefixWord ++ tailWord_248761) baseStart_248761 baseEnd_248761 := by
    simpa [prefixWord, tailWord_248761, baseEnd_248761] using wordTrace_append hprefix tailTrace_248761
  have hstable : (prefixWord ++ tailWord_248761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248761).length < 2 ^ (prefixWord ++ tailWord_248761).sum := by decide
  have hdescent : baseEnd_248761 < baseStart_248761 := by decide
  rcases family_descends (prefixWord ++ tailWord_248761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248775 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_248775 : Nat := 118140960795 + 248775 * 2 ^ 59
def prefixEnd_248775 : Nat := 4983230072969 + 3 ^ 40 * 248775 * 2
def baseEnd_248775 : Nat := 56773844365497511274849

theorem tailTrace_248775 : CollatzResearch.WordTrace tailWord_248775 prefixEnd_248775 56773844365497511274849 := by
  unfold tailWord_248775
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073569673738137232515779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6049046449158758155010519 9073569673738137232515779)
  ·
    refine ⟨13610354510607205848773669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9073569673738137232515779 13610354510607205848773669)
    ·
      refine ⟨2551941470738851096645063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13610354510607205848773669 2551941470738851096645063)
      ·
        refine ⟨3827912206108276644967595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551941470738851096645063 3827912206108276644967595)
        ·
          refine ⟨5741868309162414967451393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827912206108276644967595 5741868309162414967451393)
          ·
            refine ⟨4306401231871811225588545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741868309162414967451393 4306401231871811225588545)
            ·
              refine ⟨3229800923903858419191409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306401231871811225588545 3229800923903858419191409)
              ·
                refine ⟨2422350692927893814393557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229800923903858419191409 2422350692927893814393557)
                ·
                  refine ⟨56773844365497511274849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2422350692927893814393557 56773844365497511274849)
                  ·
                    rfl

theorem cell21_248775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_248775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248775 prefixEnd_248775 := by exact prefixLift 248775
  have htrace : WordTrace (prefixWord ++ tailWord_248775) baseStart_248775 baseEnd_248775 := by
    simpa [prefixWord, tailWord_248775, baseEnd_248775] using wordTrace_append hprefix tailTrace_248775
  have hstable : (prefixWord ++ tailWord_248775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248775).length < 2 ^ (prefixWord ++ tailWord_248775).sum := by decide
  have hdescent : baseEnd_248775 < baseStart_248775 := by decide
  rcases family_descends (prefixWord ++ tailWord_248775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248792 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_248792 : Nat := 118140960795 + 248792 * 2 ^ 59
def prefixEnd_248792 : Nat := 4983230072969 + 3 ^ 40 * 248792 * 2
def baseEnd_248792 : Nat := 56777723997109259491481

theorem tailTrace_248792 : CollatzResearch.WordTrace tailWord_248792 prefixEnd_248792 56777723997109259491481 := by
  unfold tailWord_248792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537094857338274567942315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6049459809784366090589753 4537094857338274567942315)
  ·
    refine ⟨6805642286007411851913473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4537094857338274567942315 6805642286007411851913473)
    ·
      refine ⟨5104231714505558888935105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6805642286007411851913473 5104231714505558888935105)
      ·
        refine ⟨3828173785879169166701329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5104231714505558888935105 3828173785879169166701329)
        ·
          refine ⟨2871130339409376875025997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3828173785879169166701329 2871130339409376875025997)
          ·
            refine ⟨1076673877278516328134749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2871130339409376875025997 1076673877278516328134749)
            ·
              refine ⟨403752703979443623050531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076673877278516328134749 403752703979443623050531)
              ·
                refine ⟨605629055969165434575797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403752703979443623050531 605629055969165434575797)
                ·
                  refine ⟨56777723997109259491481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605629055969165434575797 56777723997109259491481)
                  ·
                    rfl

theorem cell21_248792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_248792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248792 prefixEnd_248792 := by exact prefixLift 248792
  have htrace : WordTrace (prefixWord ++ tailWord_248792) baseStart_248792 baseEnd_248792 := by
    simpa [prefixWord, tailWord_248792, baseEnd_248792] using wordTrace_append hprefix tailTrace_248792
  have hstable : (prefixWord ++ tailWord_248792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248792).length < 2 ^ (prefixWord ++ tailWord_248792).sum := by decide
  have hdescent : baseEnd_248792 < baseStart_248792 := by decide
  rcases family_descends (prefixWord ++ tailWord_248792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248851 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_248851 : Nat := 118140960795 + 248851 * 2 ^ 59
def prefixEnd_248851 : Nat := 4983230072969 + 3 ^ 40 * 248851 * 2
def baseEnd_248851 : Nat := 56791188600938268008027

theorem tailTrace_248851 : CollatzResearch.WordTrace tailWord_248851 prefixEnd_248851 56791188600938268008027 := by
  unfold tailWord_248851
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076341621462802212282407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6050894414308534808188271 9076341621462802212282407)
  ·
    refine ⟨13614512432194203318423611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076341621462802212282407 13614512432194203318423611)
    ·
      refine ⟨20421768648291304977635417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13614512432194203318423611 20421768648291304977635417)
      ·
        refine ⟨15316326486218478733226563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20421768648291304977635417 15316326486218478733226563)
        ·
          refine ⟨22974489729327718099839845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15316326486218478733226563 22974489729327718099839845)
          ·
            refine ⟨4307716824248947143719971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22974489729327718099839845 4307716824248947143719971)
            ·
              refine ⟨6461575236373420715579957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307716824248947143719971 6461575236373420715579957)
              ·
                refine ⟨605772678410008192085621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6461575236373420715579957 605772678410008192085621)
                ·
                  refine ⟨56791188600938268008027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605772678410008192085621 56791188600938268008027)
                  ·
                    rfl

theorem cell21_248851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_248851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248851 prefixEnd_248851 := by exact prefixLift 248851
  have htrace : WordTrace (prefixWord ++ tailWord_248851) baseStart_248851 baseEnd_248851 := by
    simpa [prefixWord, tailWord_248851, baseEnd_248851] using wordTrace_append hprefix tailTrace_248851
  have hstable : (prefixWord ++ tailWord_248851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248851).length < 2 ^ (prefixWord ++ tailWord_248851).sum := by decide
  have hdescent : baseEnd_248851 < baseStart_248851 := by decide
  rcases family_descends (prefixWord ++ tailWord_248851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248868 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_248868 : Nat := 118140960795 + 248868 * 2 ^ 59
def prefixEnd_248868 : Nat := 4983230072969 + 3 ^ 40 * 248868 * 2
def baseEnd_248868 : Nat := 56795068232550016224659

theorem tailTrace_248868 : CollatzResearch.WordTrace tailWord_248868 prefixEnd_248868 56795068232550016224659 := by
  unfold tailWord_248868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538480831200607057825629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6051307774934142743767505 4538480831200607057825629)
  ·
    refine ⟨1701930311700227646684611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4538480831200607057825629 1701930311700227646684611)
    ·
      refine ⟨2552895467550341470026917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701930311700227646684611 2552895467550341470026917)
      ·
        refine ⟨478667900165689025630047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2552895467550341470026917 478667900165689025630047)
        ·
          refine ⟨718001850248533538445071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478667900165689025630047 718001850248533538445071)
          ·
            refine ⟨1077002775372800307667607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718001850248533538445071 1077002775372800307667607)
            ·
              refine ⟨1615504163059200461501411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077002775372800307667607 1615504163059200461501411)
              ·
                refine ⟨2423256244588800692252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615504163059200461501411 2423256244588800692252117)
                ·
                  refine ⟨56795068232550016224659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2423256244588800692252117 56795068232550016224659)
                  ·
                    rfl

theorem cell21_248868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_248868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248868 prefixEnd_248868 := by exact prefixLift 248868
  have htrace : WordTrace (prefixWord ++ tailWord_248868) baseStart_248868 baseEnd_248868 := by
    simpa [prefixWord, tailWord_248868, baseEnd_248868] using wordTrace_append hprefix tailTrace_248868
  have hstable : (prefixWord ++ tailWord_248868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248868).length < 2 ^ (prefixWord ++ tailWord_248868).sum := by decide
  have hdescent : baseEnd_248868 < baseStart_248868 := by decide
  rcases family_descends (prefixWord ++ tailWord_248868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248871 : List Nat := [1, 1, 7, 1, 1, 2, 3, 5]
def baseStart_248871 : Nat := 118140960795 + 248871 * 2 ^ 59
def prefixEnd_248871 : Nat := 4983230072969 + 3 ^ 40 * 248871 * 2
def baseEnd_248871 : Nat := 18931917624474225891551

theorem tailTrace_248871 : CollatzResearch.WordTrace tailWord_248871 prefixEnd_248871 18931917624474225891551 := by
  unfold tailWord_248871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077071081390345628010467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6051380720926897085340311 9077071081390345628010467)
  ·
    refine ⟨13615606622085518442015701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9077071081390345628010467 13615606622085518442015701)
    ·
      refine ⟨319115780205129338484743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13615606622085518442015701 319115780205129338484743)
      ·
        refine ⟨478673670307694007727115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319115780205129338484743 478673670307694007727115)
        ·
          refine ⟨718010505461541011590673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478673670307694007727115 718010505461541011590673)
          ·
            refine ⟨538507879096155758693005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718010505461541011590673 538507879096155758693005)
            ·
              refine ⟨201940454661058409509877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538507879096155758693005 201940454661058409509877)
              ·
                refine ⟨18931917624474225891551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201940454661058409509877 18931917624474225891551)
                ·
                  rfl

theorem cell21_248871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 5].length) (baseStart_248871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248871 prefixEnd_248871 := by exact prefixLift 248871
  have htrace : WordTrace (prefixWord ++ tailWord_248871) baseStart_248871 baseEnd_248871 := by
    simpa [prefixWord, tailWord_248871, baseEnd_248871] using wordTrace_append hprefix tailTrace_248871
  have hstable : (prefixWord ++ tailWord_248871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248871).length < 2 ^ (prefixWord ++ tailWord_248871).sum := by decide
  have hdescent : baseEnd_248871 < baseStart_248871 := by decide
  rcases family_descends (prefixWord ++ tailWord_248871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248882 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_248882 : Nat := 118140960795 + 248882 * 2 ^ 59
def prefixEnd_248882 : Nat := 4983230072969 + 3 ^ 40 * 248882 * 2
def baseEnd_248882 : Nat := 56798263223289102991297

theorem tailTrace_248882 : CollatzResearch.WordTrace tailWord_248882 prefixEnd_248882 56798263223289102991297 := by
  unfold tailWord_248882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269368071087623626665225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6051648189566996337773933 2269368071087623626665225)
  ·
    refine ⟨1702026053315717719998919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2269368071087623626665225 1702026053315717719998919)
    ·
      refine ⟨2553039079973576579998379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702026053315717719998919 2553039079973576579998379)
      ·
        refine ⟨3829558619960364869997569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553039079973576579998379 3829558619960364869997569)
        ·
          refine ⟨2872168964970273652498177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3829558619960364869997569 2872168964970273652498177)
          ·
            refine ⟨2154126723727705239373633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872168964970273652498177 2154126723727705239373633)
            ·
              refine ⟨1615595042795778929530225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154126723727705239373633 1615595042795778929530225)
              ·
                refine ⟨1211696282096834197147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615595042795778929530225 1211696282096834197147669)
                ·
                  refine ⟨56798263223289102991297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1211696282096834197147669 56798263223289102991297)
                  ·
                    rfl

theorem cell21_248882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_248882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248882 prefixEnd_248882 := by exact prefixLift 248882
  have htrace : WordTrace (prefixWord ++ tailWord_248882) baseStart_248882 baseEnd_248882 := by
    simpa [prefixWord, tailWord_248882, baseEnd_248882] using wordTrace_append hprefix tailTrace_248882
  have hstable : (prefixWord ++ tailWord_248882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248882).length < 2 ^ (prefixWord ++ tailWord_248882).sum := by decide
  have hdescent : baseEnd_248882 < baseStart_248882 := by decide
  rcases family_descends (prefixWord ++ tailWord_248882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248896 : List Nat := [2, 1, 1, 2, 2, 3, 10]
def baseStart_248896 : Nat := 118140960795 + 248896 * 2 ^ 59
def prefixEnd_248896 : Nat := 4983230072969 + 3 ^ 40 * 248896 * 2
def baseEnd_248896 : Nat := 6311273134892021084215

theorem tailTrace_248896 : CollatzResearch.WordTrace tailWord_248896 prefixEnd_248896 6311273134892021084215 := by
  unfold tailWord_248896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538991453149887448835271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6051988604199849931780361 4538991453149887448835271)
  ·
    refine ⟨6808487179724831173252907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4538991453149887448835271 6808487179724831173252907)
    ·
      refine ⟨10212730769587246759879361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6808487179724831173252907 10212730769587246759879361)
      ·
        refine ⟨7659548077190435069909521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10212730769587246759879361 7659548077190435069909521)
        ·
          refine ⟨5744661057892826302432141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7659548077190435069909521 5744661057892826302432141)
          ·
            refine ⟨2154247896709809863412053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5744661057892826302432141 2154247896709809863412053)
            ·
              refine ⟨6311273134892021084215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2154247896709809863412053 6311273134892021084215)
              ·
                rfl

theorem cell21_248896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 10].length) (baseStart_248896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248896 prefixEnd_248896 := by exact prefixLift 248896
  have htrace : WordTrace (prefixWord ++ tailWord_248896) baseStart_248896 baseEnd_248896 := by
    simpa [prefixWord, tailWord_248896, baseEnd_248896] using wordTrace_append hprefix tailTrace_248896
  have hstable : (prefixWord ++ tailWord_248896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248896).length < 2 ^ (prefixWord ++ tailWord_248896).sum := by decide
  have hdescent : baseEnd_248896 < baseStart_248896 := by decide
  rcases family_descends (prefixWord ++ tailWord_248896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248902 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_248902 : Nat := 118140960795 + 248902 * 2 ^ 59
def prefixEnd_248902 : Nat := 4983230072969 + 3 ^ 40 * 248902 * 2
def baseEnd_248902 : Nat := 56802827495773512657923

theorem tailTrace_248902 : CollatzResearch.WordTrace tailWord_248902 prefixEnd_248902 56802827495773512657923 := by
  unfold tailWord_248902
  simp only [CollatzResearch.WordTrace]
  refine ⟨283693804508688685074655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6052134496185358614925973 283693804508688685074655)
  ·
    refine ⟨425540706763033027611983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283693804508688685074655 425540706763033027611983)
    ·
      refine ⟨638311060144549541417975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425540706763033027611983 638311060144549541417975)
      ·
        refine ⟨957466590216824312126963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638311060144549541417975 957466590216824312126963)
        ·
          refine ⟨1436199885325236468190445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957466590216824312126963 1436199885325236468190445)
          ·
            refine ⟨538574956996963675571417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1436199885325236468190445 538574956996963675571417)
            ·
              refine ⟨403931217747722756678563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538574956996963675571417 403931217747722756678563)
              ·
                refine ⟨605896826621584135017845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403931217747722756678563 605896826621584135017845)
                ·
                  refine ⟨56802827495773512657923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605896826621584135017845 56802827495773512657923)
                  ·
                    rfl

theorem cell21_248902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_248902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248902 prefixEnd_248902 := by exact prefixLift 248902
  have htrace : WordTrace (prefixWord ++ tailWord_248902) baseStart_248902 baseEnd_248902 := by
    simpa [prefixWord, tailWord_248902, baseEnd_248902] using wordTrace_append hprefix tailTrace_248902
  have hstable : (prefixWord ++ tailWord_248902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248902).length < 2 ^ (prefixWord ++ tailWord_248902).sum := by decide
  have hdescent : baseEnd_248902 < baseStart_248902 := by decide
  rcases family_descends (prefixWord ++ tailWord_248902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248927 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_248927 : Nat := 118140960795 + 248927 * 2 ^ 59
def prefixEnd_248927 : Nat := 4983230072969 + 3 ^ 40 * 248927 * 2
def baseEnd_248927 : Nat := 56808532836379024741205

theorem tailTrace_248927 : CollatzResearch.WordTrace tailWord_248927 prefixEnd_248927 56808532836379024741205 := by
  unfold tailWord_248927
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079113569187467192049035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6052742379458311461366023 9079113569187467192049035)
  ·
    refine ⟨13618670353781200788073553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9079113569187467192049035 13618670353781200788073553)
    ·
      refine ⟨10214002765335900591055165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13618670353781200788073553 10214002765335900591055165)
      ·
        refine ⟨3830251037000962721645687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10214002765335900591055165 3830251037000962721645687)
        ·
          refine ⟨5745376555501444082468531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830251037000962721645687 5745376555501444082468531)
          ·
            refine ⟨8618064833252166123702797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745376555501444082468531 8618064833252166123702797)
            ·
              refine ⟨3231774312469562296388549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8618064833252166123702797 3231774312469562296388549)
              ·
                refine ⟨605957683588042930572853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3231774312469562296388549 605957683588042930572853)
                ·
                  refine ⟨56808532836379024741205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605957683588042930572853 56808532836379024741205)
                  ·
                    rfl

theorem cell21_248927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_248927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248927 prefixEnd_248927 := by exact prefixLift 248927
  have htrace : WordTrace (prefixWord ++ tailWord_248927) baseStart_248927 baseEnd_248927 := by
    simpa [prefixWord, tailWord_248927, baseEnd_248927] using wordTrace_append hprefix tailTrace_248927
  have hstable : (prefixWord ++ tailWord_248927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248927).length < 2 ^ (prefixWord ++ tailWord_248927).sum := by decide
  have hdescent : baseEnd_248927 < baseStart_248927 := by decide
  rcases family_descends (prefixWord ++ tailWord_248927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248930 : List Nat := [3, 3, 2, 2, 1, 2, 1, 7]
def baseStart_248930 : Nat := 118140960795 + 248930 * 2 ^ 59
def prefixEnd_248930 : Nat := 4983230072969 + 3 ^ 40 * 248930 * 2
def baseEnd_248930 : Nat := 18936405825750562063733

theorem tailTrace_248930 : CollatzResearch.WordTrace tailWord_248930 prefixEnd_248930 18936405825750562063733 := by
  unfold tailWord_248930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269805747044149676102061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6052815325451065802938829 2269805747044149676102061)
  ·
    refine ⟨851177155141556128538273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2269805747044149676102061 851177155141556128538273)
    ·
      refine ⟨638382866356167096403705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 851177155141556128538273 638382866356167096403705)
      ·
        refine ⟨478787149767125322302779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638382866356167096403705 478787149767125322302779)
        ·
          refine ⟨718180724650687983454169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478787149767125322302779 718180724650687983454169)
          ·
            refine ⟨538635543488015987590627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718180724650687983454169 538635543488015987590627)
            ·
              refine ⟨807953315232023981385941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538635543488015987590627 807953315232023981385941)
              ·
                refine ⟨18936405825750562063733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 807953315232023981385941 18936405825750562063733)
                ·
                  rfl

theorem cell21_248930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_248930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248930 prefixEnd_248930 := by exact prefixLift 248930
  have htrace : WordTrace (prefixWord ++ tailWord_248930) baseStart_248930 baseEnd_248930 := by
    simpa [prefixWord, tailWord_248930, baseEnd_248930] using wordTrace_append hprefix tailTrace_248930
  have hstable : (prefixWord ++ tailWord_248930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248930).length < 2 ^ (prefixWord ++ tailWord_248930).sum := by decide
  have hdescent : baseEnd_248930 < baseStart_248930 := by decide
  rcases family_descends (prefixWord ++ tailWord_248930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248936 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_248936 : Nat := 118140960795 + 248936 * 2 ^ 59
def prefixEnd_248936 : Nat := 4983230072969 + 3 ^ 40 * 248936 * 2
def baseEnd_248936 : Nat := 56810586758997009091187

theorem tailTrace_248936 : CollatzResearch.WordTrace tailWord_248936 prefixEnd_248936 56810586758997009091187 := by
  unfold tailWord_248936
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539720913077430864563331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6052961217436574486084441 4539720913077430864563331)
  ·
    refine ⟨6809581369616146296844997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539720913077430864563331 6809581369616146296844997)
    ·
      refine ⟨1276796506803027430658437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6809581369616146296844997 1276796506803027430658437)
      ·
        refine ⟨239399345025567643248457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1276796506803027430658437 239399345025567643248457)
        ·
          refine ⟨179549508769175732436343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239399345025567643248457 179549508769175732436343)
          ·
            refine ⟨269324263153763598654515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179549508769175732436343 269324263153763598654515)
            ·
              refine ⟨403986394730645397981773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269324263153763598654515 403986394730645397981773)
              ·
                refine ⟨151494898023992024243165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403986394730645397981773 151494898023992024243165)
                ·
                  refine ⟨56810586758997009091187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151494898023992024243165 56810586758997009091187)
                  ·
                    rfl

theorem cell21_248936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_248936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248936 prefixEnd_248936 := by exact prefixLift 248936
  have htrace : WordTrace (prefixWord ++ tailWord_248936) baseStart_248936 baseEnd_248936 := by
    simpa [prefixWord, tailWord_248936, baseEnd_248936] using wordTrace_append hprefix tailTrace_248936
  have hstable : (prefixWord ++ tailWord_248936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248936).length < 2 ^ (prefixWord ++ tailWord_248936).sum := by decide
  have hdescent : baseEnd_248936 < baseStart_248936 := by decide
  rcases family_descends (prefixWord ++ tailWord_248936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248961 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 5]
def baseStart_248961 : Nat := 118140960795 + 248961 * 2 ^ 59
def prefixEnd_248961 : Nat := 4983230072969 + 3 ^ 40 * 248961 * 2
def baseEnd_248961 : Nat := 56816292099602521174469

theorem tailTrace_248961 : CollatzResearch.WordTrace tailWord_248961 prefixEnd_248961 56816292099602521174469 := by
  unfold tailWord_248961
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080353651064290998786737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6053569100709527332524491 9080353651064290998786737)
  ·
    refine ⟨6810265238298218249090053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9080353651064290998786737 6810265238298218249090053)
    ·
      refine ⟨1276924732180915921704385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6810265238298218249090053 1276924732180915921704385)
      ·
        refine ⟨957693549135686941278289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276924732180915921704385 957693549135686941278289)
        ·
          refine ⟨718270161851765205958717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957693549135686941278289 718270161851765205958717)
          ·
            refine ⟨269351310694411952234519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718270161851765205958717 269351310694411952234519)
            ·
              refine ⟨404026966041617928351779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269351310694411952234519 404026966041617928351779)
              ·
                refine ⟨606040449062426892527669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404026966041617928351779 606040449062426892527669)
                ·
                  refine ⟨56816292099602521174469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 606040449062426892527669 56816292099602521174469)
                  ·
                    rfl

theorem cell21_248961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_248961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_248961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_248961 prefixEnd_248961 := by exact prefixLift 248961
  have htrace : WordTrace (prefixWord ++ tailWord_248961) baseStart_248961 baseEnd_248961 := by
    simpa [prefixWord, tailWord_248961, baseEnd_248961] using wordTrace_append hprefix tailTrace_248961
  have hstable : (prefixWord ++ tailWord_248961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248961).length < 2 ^ (prefixWord ++ tailWord_248961).sum := by decide
  have hdescent : baseEnd_248961 < baseStart_248961 := by decide
  rcases family_descends (prefixWord ++ tailWord_248961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249141 : List Nat := [1, 3, 3, 1, 2, 3, 2, 6]
def baseStart_249141 : Nat := 118140960795 + 249141 * 2 ^ 59
def prefixEnd_249141 : Nat := 4983230072969 + 3 ^ 40 * 249141 * 2
def baseEnd_249141 : Nat := 18952456850654069391367

theorem tailTrace_249141 : CollatzResearch.WordTrace tailWord_249141 prefixEnd_249141 18952456850654069391367 := by
  unfold tailWord_249141
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086918790412181740339277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6057945860274787826892851 9086918790412181740339277)
  ·
    refine ⟨3407594546404568152627229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9086918790412181740339277 3407594546404568152627229)
    ·
      refine ⟨1277847954901713057235211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3407594546404568152627229 1277847954901713057235211)
      ·
        refine ⟨1916771932352569585852817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277847954901713057235211 1916771932352569585852817)
        ·
          refine ⟨1437578949264427189389613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916771932352569585852817 1437578949264427189389613)
          ·
            refine ⟨539092105974160196021105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1437578949264427189389613 539092105974160196021105)
            ·
              refine ⟨404319079480620147015829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539092105974160196021105 404319079480620147015829)
              ·
                refine ⟨18952456850654069391367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 404319079480620147015829 18952456850654069391367)
                ·
                  rfl

theorem cell21_249141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_249141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249141 prefixEnd_249141 := by exact prefixLift 249141
  have htrace : WordTrace (prefixWord ++ tailWord_249141) baseStart_249141 baseEnd_249141 := by
    simpa [prefixWord, tailWord_249141, baseEnd_249141] using wordTrace_append hprefix tailTrace_249141
  have hstable : (prefixWord ++ tailWord_249141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249141).length < 2 ^ (prefixWord ++ tailWord_249141).sum := by decide
  have hdescent : baseEnd_249141 < baseStart_249141 := by decide
  rcases family_descends (prefixWord ++ tailWord_249141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249181 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 3]
def baseStart_249181 : Nat := 118140960795 + 249181 * 2 ^ 59
def prefixEnd_249181 : Nat := 4983230072969 + 3 ^ 40 * 249181 * 2
def baseEnd_249181 : Nat := 56866499096931027507353

theorem tailTrace_249181 : CollatzResearch.WordTrace tailWord_249181 prefixEnd_249181 56866499096931027507353 := by
  unfold tailWord_249181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088377710267268571795397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6058918473511512381196931 9088377710267268571795397)
  ·
    refine ⟨1704070820675112857211637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9088377710267268571795397 1704070820675112857211637)
    ·
      refine ⟨159756639438291830363591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1704070820675112857211637 159756639438291830363591)
      ·
        refine ⟨239634959157437745545387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159756639438291830363591 239634959157437745545387)
        ·
          refine ⟨359452438736156618318081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239634959157437745545387 359452438736156618318081)
          ·
            refine ⟨269589329052117463738561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359452438736156618318081 269589329052117463738561)
            ·
              refine ⟨202191996789088097803921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269589329052117463738561 202191996789088097803921)
              ·
                refine ⟨151643997591816073352941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202191996789088097803921 151643997591816073352941)
                ·
                  refine ⟨56866499096931027507353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151643997591816073352941 56866499096931027507353)
                  ·
                    rfl

theorem cell21_249181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_249181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249181 prefixEnd_249181 := by exact prefixLift 249181
  have htrace : WordTrace (prefixWord ++ tailWord_249181) baseStart_249181 baseEnd_249181 := by
    simpa [prefixWord, tailWord_249181, baseEnd_249181] using wordTrace_append hprefix tailTrace_249181
  have hstable : (prefixWord ++ tailWord_249181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249181).length < 2 ^ (prefixWord ++ tailWord_249181).sum := by decide
  have hdescent : baseEnd_249181 < baseStart_249181 := by decide
  rcases family_descends (prefixWord ++ tailWord_249181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249234 : List Nat := [3, 2, 3, 3, 1, 1, 8]
def baseStart_249234 : Nat := 118140960795 + 249234 * 2 ^ 59
def prefixEnd_249234 : Nat := 4983230072969 + 3 ^ 40 * 249234 * 2
def baseEnd_249234 : Nat := 6319843824334968124879

theorem tailTrace_249234 : CollatzResearch.WordTrace tailWord_249234 prefixEnd_249234 6319843824334968124879 := by
  unfold tailWord_249234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272577694768814655868689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6060207186050172415649837 2272577694768814655868689)
  ·
    refine ⟨1704433271076610991901517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2272577694768814655868689 1704433271076610991901517)
    ·
      refine ⟨639162476653729121963069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1704433271076610991901517 639162476653729121963069)
      ·
        refine ⟨239685928745148420736151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639162476653729121963069 239685928745148420736151)
        ·
          refine ⟨359528893117722631104227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239685928745148420736151 359528893117722631104227)
          ·
            refine ⟨539293339676583946656341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359528893117722631104227 539293339676583946656341)
            ·
              refine ⟨6319843824334968124879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 539293339676583946656341 6319843824334968124879)
              ·
                rfl

theorem cell21_249234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 8].length) (baseStart_249234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249234 prefixEnd_249234 := by exact prefixLift 249234
  have htrace : WordTrace (prefixWord ++ tailWord_249234) baseStart_249234 baseEnd_249234 := by
    simpa [prefixWord, tailWord_249234, baseEnd_249234] using wordTrace_append hprefix tailTrace_249234
  have hstable : (prefixWord ++ tailWord_249234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249234).length < 2 ^ (prefixWord ++ tailWord_249234).sum := by decide
  have hdescent : baseEnd_249234 < baseStart_249234 := by decide
  rcases family_descends (prefixWord ++ tailWord_249234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249248 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_249248 : Nat := 118140960795 + 249248 * 2 ^ 59
def prefixEnd_249248 : Nat := 4983230072969 + 3 ^ 40 * 249248 * 2
def baseEnd_249248 : Nat := 56881789409753799890549

theorem tailTrace_249248 : CollatzResearch.WordTrace tailWord_249248 prefixEnd_249248 56881789409753799890549 := by
  unfold tailWord_249248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545410700512269507242199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6060547600683026009656265 4545410700512269507242199)
  ·
    refine ⟨6818116050768404260863299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545410700512269507242199 6818116050768404260863299)
    ·
      refine ⟨10227174076152606391294949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818116050768404260863299 10227174076152606391294949)
      ·
        refine ⟨1917595139278613698367803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10227174076152606391294949 1917595139278613698367803)
        ·
          refine ⟨2876392708917920547551705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917595139278613698367803 2876392708917920547551705)
          ·
            refine ⟨2157294531688440410663779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876392708917920547551705 2157294531688440410663779)
            ·
              refine ⟨3235941797532660615995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157294531688440410663779 3235941797532660615995669)
              ·
                refine ⟨151684771759343466374797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3235941797532660615995669 151684771759343466374797)
                ·
                  refine ⟨56881789409753799890549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151684771759343466374797 56881789409753799890549)
                  ·
                    rfl

theorem cell21_249248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_249248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249248 prefixEnd_249248 := by exact prefixLift 249248
  have htrace : WordTrace (prefixWord ++ tailWord_249248) baseStart_249248 baseEnd_249248 := by
    simpa [prefixWord, tailWord_249248, baseEnd_249248] using wordTrace_append hprefix tailTrace_249248
  have hstable : (prefixWord ++ tailWord_249248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249248).length < 2 ^ (prefixWord ++ tailWord_249248).sum := by decide
  have hdescent : baseEnd_249248 < baseStart_249248 := by decide
  rcases family_descends (prefixWord ++ tailWord_249248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249350 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_249350 : Nat := 118140960795 + 249350 * 2 ^ 59
def prefixEnd_249350 : Nat := 4983230072969 + 3 ^ 40 * 249350 * 2
def baseEnd_249350 : Nat := 56905067199424289190341

theorem tailTrace_249350 : CollatzResearch.WordTrace tailWord_249350 prefixEnd_249350 56905067199424289190341 := by
  unfold tailWord_249350
  simp only [CollatzResearch.WordTrace]
  refine ⟨284204426457969076084297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6063027764436673623131669 284204426457969076084297)
  ·
    refine ⟨213153319843476807063223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284204426457969076084297 213153319843476807063223)
    ·
      refine ⟨319729979765215210594835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213153319843476807063223 319729979765215210594835)
      ·
        refine ⟨479594969647822815892253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319729979765215210594835 479594969647822815892253)
        ·
          refine ⟨179848113617933555959595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479594969647822815892253 179848113617933555959595)
          ·
            refine ⟨269772170426900333939393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179848113617933555959595 269772170426900333939393)
            ·
              refine ⟨202329127820175250454545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269772170426900333939393 202329127820175250454545)
              ·
                refine ⟨151746845865131437840909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202329127820175250454545 151746845865131437840909)
                ·
                  refine ⟨56905067199424289190341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151746845865131437840909 56905067199424289190341)
                  ·
                    rfl

theorem cell21_249350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_249350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249350 prefixEnd_249350 := by exact prefixLift 249350
  have htrace : WordTrace (prefixWord ++ tailWord_249350) baseStart_249350 baseEnd_249350 := by
    simpa [prefixWord, tailWord_249350, baseEnd_249350] using wordTrace_append hprefix tailTrace_249350
  have hstable : (prefixWord ++ tailWord_249350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249350).length < 2 ^ (prefixWord ++ tailWord_249350).sum := by decide
  have hdescent : baseEnd_249350 < baseStart_249350 := by decide
  rcases family_descends (prefixWord ++ tailWord_249350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249355 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_249355 : Nat := 118140960795 + 249355 * 2 ^ 59
def prefixEnd_249355 : Nat := 4983230072969 + 3 ^ 40 * 249355 * 2
def baseEnd_249355 : Nat := 56906208267545391606997

theorem tailTrace_249355 : CollatzResearch.WordTrace tailWord_249355 prefixEnd_249355 56906208267545391606997 := by
  unfold tailWord_249355
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094724011636896288629519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6063149341091264192419679 9094724011636896288629519)
  ·
    refine ⟨13642086017455344432944279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9094724011636896288629519 13642086017455344432944279)
    ·
      refine ⟨20463129026183016649416419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642086017455344432944279 20463129026183016649416419)
      ·
        refine ⟨30694693539274524974124629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463129026183016649416419 30694693539274524974124629)
        ·
          refine ⟨359703439913373339540523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 30694693539274524974124629 359703439913373339540523)
          ·
            refine ⟨539555159870060009310785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359703439913373339540523 539555159870060009310785)
            ·
              refine ⟨404666369902545006983089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539555159870060009310785 404666369902545006983089)
              ·
                refine ⟨303499777426908755237317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404666369902545006983089 303499777426908755237317)
                ·
                  refine ⟨56906208267545391606997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303499777426908755237317 56906208267545391606997)
                  ·
                    rfl

theorem cell21_249355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_249355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249355 prefixEnd_249355 := by exact prefixLift 249355
  have htrace : WordTrace (prefixWord ++ tailWord_249355) baseStart_249355 baseEnd_249355 := by
    simpa [prefixWord, tailWord_249355, baseEnd_249355] using wordTrace_append hprefix tailTrace_249355
  have hstable : (prefixWord ++ tailWord_249355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249355).length < 2 ^ (prefixWord ++ tailWord_249355).sum := by decide
  have hdescent : baseEnd_249355 < baseStart_249355 := by decide
  rcases family_descends (prefixWord ++ tailWord_249355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249400 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_249400 : Nat := 118140960795 + 249400 * 2 ^ 59
def prefixEnd_249400 : Nat := 4983230072969 + 3 ^ 40 * 249400 * 2
def baseEnd_249400 : Nat := 56916477880635313356905

theorem tailTrace_249400 : CollatzResearch.WordTrace tailWord_249400 prefixEnd_249400 56916477880635313356905 := by
  unfold tailWord_249400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548182648236934487008827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6064243530982579316011769 4548182648236934487008827)
  ·
    refine ⟨6822273972355401730513241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4548182648236934487008827 6822273972355401730513241)
    ·
      refine ⟨5116705479266551297884931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6822273972355401730513241 5116705479266551297884931)
      ·
        refine ⟨7675058218899826946827397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116705479266551297884931 7675058218899826946827397)
        ·
          refine ⟨1439073416043717552530137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7675058218899826946827397 1439073416043717552530137)
          ·
            refine ⟨1079305062032788164397603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439073416043717552530137 1079305062032788164397603)
            ·
              refine ⟨1618957593049182246596405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079305062032788164397603 1618957593049182246596405)
              ·
                refine ⟨151777274348360835618413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1618957593049182246596405 151777274348360835618413)
                ·
                  refine ⟨56916477880635313356905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151777274348360835618413 56916477880635313356905)
                  ·
                    rfl

theorem cell21_249400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_249400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249400 prefixEnd_249400 := by exact prefixLift 249400
  have htrace : WordTrace (prefixWord ++ tailWord_249400) baseStart_249400 baseEnd_249400 := by
    simpa [prefixWord, tailWord_249400, baseEnd_249400] using wordTrace_append hprefix tailTrace_249400
  have hstable : (prefixWord ++ tailWord_249400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249400).length < 2 ^ (prefixWord ++ tailWord_249400).sum := by decide
  have hdescent : baseEnd_249400 < baseStart_249400 := by decide
  rcases family_descends (prefixWord ++ tailWord_249400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249428 : List Nat := [2, 4, 1, 1, 1, 2, 2, 8]
def baseStart_249428 : Nat := 118140960795 + 249428 * 2 ^ 59
def prefixEnd_249428 : Nat := 4983230072969 + 3 ^ 40 * 249428 * 2
def baseEnd_249428 : Nat := 18974289287371162296727

theorem tailTrace_249428 : CollatzResearch.WordTrace tailWord_249428 prefixEnd_249428 18974289287371162296727 := by
  unfold tailWord_249428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548693270186214878018469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6064924360248286504024625 4548693270186214878018469)
  ·
    refine ⟨852879988159915289628463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4548693270186214878018469 852879988159915289628463)
    ·
      refine ⟨1279319982239872934442695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852879988159915289628463 1279319982239872934442695)
      ·
        refine ⟨1918979973359809401664043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279319982239872934442695 1918979973359809401664043)
        ·
          refine ⟨2878469960039714102496065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918979973359809401664043 2878469960039714102496065)
          ·
            refine ⟨2158852470029785576872049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878469960039714102496065 2158852470029785576872049)
            ·
              refine ⟨1619139352522339182654037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158852470029785576872049 1619139352522339182654037)
              ·
                refine ⟨18974289287371162296727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1619139352522339182654037 18974289287371162296727)
                ·
                  rfl

theorem cell21_249428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_249428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249428 prefixEnd_249428 := by exact prefixLift 249428
  have htrace : WordTrace (prefixWord ++ tailWord_249428) baseStart_249428 baseEnd_249428 := by
    simpa [prefixWord, tailWord_249428, baseEnd_249428] using wordTrace_append hprefix tailTrace_249428
  have hstable : (prefixWord ++ tailWord_249428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249428).length < 2 ^ (prefixWord ++ tailWord_249428).sum := by decide
  have hdescent : baseEnd_249428 < baseStart_249428 := by decide
  rcases family_descends (prefixWord ++ tailWord_249428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249431 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 4]
def baseStart_249431 : Nat := 118140960795 + 249431 * 2 ^ 59
def prefixEnd_249431 : Nat := 4983230072969 + 3 ^ 40 * 249431 * 2
def baseEnd_249431 : Nat := 56923552502986148340175

theorem tailTrace_249431 : CollatzResearch.WordTrace tailWord_249431 prefixEnd_249431 56923552502986148340175 := by
  unfold tailWord_249431
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097495959361561268396147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6064997306241040845597431 9097495959361561268396147)
  ·
    refine ⟨13646243939042341902594221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9097495959361561268396147 13646243939042341902594221)
    ·
      refine ⟨5117341477140878213472833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13646243939042341902594221 5117341477140878213472833)
      ·
        refine ⟨3838006107855658660104625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5117341477140878213472833 3838006107855658660104625)
        ·
          refine ⟨2878504580891743995078469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3838006107855658660104625 2878504580891743995078469)
          ·
            refine ⟨539719608917201999077213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2878504580891743995078469 539719608917201999077213)
            ·
              refine ⟨202394853343950749653955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539719608917201999077213 202394853343950749653955)
              ·
                refine ⟨303592280015926124480933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202394853343950749653955 303592280015926124480933)
                ·
                  refine ⟨56923552502986148340175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303592280015926124480933 56923552502986148340175)
                  ·
                    rfl

theorem cell21_249431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4].length) (baseStart_249431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249431 prefixEnd_249431 := by exact prefixLift 249431
  have htrace : WordTrace (prefixWord ++ tailWord_249431) baseStart_249431 baseEnd_249431 := by
    simpa [prefixWord, tailWord_249431, baseEnd_249431] using wordTrace_append hprefix tailTrace_249431
  have hstable : (prefixWord ++ tailWord_249431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249431).length < 2 ^ (prefixWord ++ tailWord_249431).sum := by decide
  have hdescent : baseEnd_249431 < baseStart_249431 := by decide
  rcases family_descends (prefixWord ++ tailWord_249431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249445 : List Nat := [1, 3, 1, 3, 3, 1, 4, 5]
def baseStart_249445 : Nat := 118140960795 + 249445 * 2 ^ 59
def prefixEnd_249445 : Nat := 4983230072969 + 3 ^ 40 * 249445 * 2
def baseEnd_249445 : Nat := 18975582497908411702271

theorem tailTrace_249445 : CollatzResearch.WordTrace tailWord_249445 prefixEnd_249445 18975582497908411702271 := by
  unfold tailWord_249445
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098006581310841659405789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6065337720873894439603859 9098006581310841659405789)
  ·
    refine ⟨3411752467991565622277171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9098006581310841659405789 3411752467991565622277171)
    ·
      refine ⟨5117628701987348433415757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3411752467991565622277171 5117628701987348433415757)
      ·
        refine ⟨1919110763245255662530909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5117628701987348433415757 1919110763245255662530909)
        ·
          refine ⟨719666536216970873449091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1919110763245255662530909 719666536216970873449091)
          ·
            refine ⟨1079499804325456310173637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719666536216970873449091 1079499804325456310173637)
            ·
              refine ⟨202406213311023058157557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1079499804325456310173637 202406213311023058157557)
              ·
                refine ⟨18975582497908411702271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202406213311023058157557 18975582497908411702271)
                ·
                  rfl

theorem cell21_249445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 5].length) (baseStart_249445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249445 prefixEnd_249445 := by exact prefixLift 249445
  have htrace : WordTrace (prefixWord ++ tailWord_249445) baseStart_249445 baseEnd_249445 := by
    simpa [prefixWord, tailWord_249445, baseEnd_249445] using wordTrace_append hprefix tailTrace_249445
  have hstable : (prefixWord ++ tailWord_249445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249445).length < 2 ^ (prefixWord ++ tailWord_249445).sum := by decide
  have hdescent : baseEnd_249445 < baseStart_249445 := by decide
  rcases family_descends (prefixWord ++ tailWord_249445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249504 : List Nat := [2, 1, 1, 4, 3, 1, 2, 7]
def baseStart_249504 : Nat := 118140960795 + 249504 * 2 ^ 59
def prefixEnd_249504 : Nat := 4983230072969 + 3 ^ 40 * 249504 * 2
def baseEnd_249504 : Nat := 18980070699184747874453

theorem tailTrace_249504 : CollatzResearch.WordTrace tailWord_249504 prefixEnd_249504 18980070699184747874453 := by
  unfold tailWord_249504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550079244048547367901783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6066772325398063157202377 4550079244048547367901783)
  ·
    refine ⟨6825118866072821051852675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4550079244048547367901783 6825118866072821051852675)
    ·
      refine ⟨10237678299109231577779013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825118866072821051852675 10237678299109231577779013)
      ·
        refine ⟨1919564681082980920833565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10237678299109231577779013 1919564681082980920833565)
        ·
          refine ⟨719836755406117845312587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1919564681082980920833565 719836755406117845312587)
          ·
            refine ⟨1079755133109176767968881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719836755406117845312587 1079755133109176767968881)
            ·
              refine ⟨809816349831882575976661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079755133109176767968881 809816349831882575976661)
              ·
                refine ⟨18980070699184747874453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 809816349831882575976661 18980070699184747874453)
                ·
                  rfl

theorem cell21_249504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_249504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249504 prefixEnd_249504 := by exact prefixLift 249504
  have htrace : WordTrace (prefixWord ++ tailWord_249504) baseStart_249504 baseEnd_249504 := by
    simpa [prefixWord, tailWord_249504, baseEnd_249504] using wordTrace_append hprefix tailTrace_249504
  have hstable : (prefixWord ++ tailWord_249504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249504).length < 2 ^ (prefixWord ++ tailWord_249504).sum := by decide
  have hdescent : baseEnd_249504 < baseStart_249504 := by decide
  rcases family_descends (prefixWord ++ tailWord_249504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249569 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 3]
def baseStart_249569 : Nat := 118140960795 + 249569 * 2 ^ 59
def prefixEnd_249569 : Nat := 4983230072969 + 3 ^ 40 * 249569 * 2
def baseEnd_249569 : Nat := 56955045983128575039893

theorem tailTrace_249569 : CollatzResearch.WordTrace tailWord_249569 prefixEnd_249569 56955045983128575039893 := by
  unfold tailWord_249569
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102529232861610836919761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6068352821907740557946507 9102529232861610836919761)
  ·
    refine ⟨6826896924646208127689821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9102529232861610836919761 6826896924646208127689821)
    ·
      refine ⟨2560086346742328047883683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6826896924646208127689821 2560086346742328047883683)
      ·
        refine ⟨3840129520113492071825525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560086346742328047883683 3840129520113492071825525)
        ·
          refine ⟨360012142510639881733643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3840129520113492071825525 360012142510639881733643)
          ·
            refine ⟨540018213765959822600465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360012142510639881733643 540018213765959822600465)
            ·
              refine ⟨405013660324469866950349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540018213765959822600465 405013660324469866950349)
              ·
                refine ⟨151880122621676200106381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405013660324469866950349 151880122621676200106381)
                ·
                  refine ⟨56955045983128575039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151880122621676200106381 56955045983128575039893)
                  ·
                    rfl

theorem cell21_249569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_249569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249569 prefixEnd_249569 := by exact prefixLift 249569
  have htrace : WordTrace (prefixWord ++ tailWord_249569) baseStart_249569 baseEnd_249569 := by
    simpa [prefixWord, tailWord_249569, baseEnd_249569] using wordTrace_append hprefix tailTrace_249569
  have hstable : (prefixWord ++ tailWord_249569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249569).length < 2 ^ (prefixWord ++ tailWord_249569).sum := by decide
  have hdescent : baseEnd_249569 < baseStart_249569 := by decide
  rcases family_descends (prefixWord ++ tailWord_249569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249606 : List Nat := [6, 2, 2, 1, 1, 2, 2, 5]
def baseStart_249606 : Nat := 118140960795 + 249606 * 2 ^ 59
def prefixEnd_249606 : Nat := 4983230072969 + 3 ^ 40 * 249606 * 2
def baseEnd_249606 : Nat := 18987829962408244307717

theorem tailTrace_249606 : CollatzResearch.WordTrace tailWord_249606 prefixEnd_249606 18987829962408244307717 := by
  unfold tailWord_249606
  simp only [CollatzResearch.WordTrace]
  refine ⟨284496210428986442375521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6069252489151710770677781 284496210428986442375521)
  ·
    refine ⟨213372157821739831781641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284496210428986442375521 213372157821739831781641)
    ·
      refine ⟨160029118366304873836231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213372157821739831781641 160029118366304873836231)
      ·
        refine ⟨240043677549457310754347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160029118366304873836231 240043677549457310754347)
        ·
          refine ⟨360065516324185966131521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240043677549457310754347 360065516324185966131521)
          ·
            refine ⟨270049137243139474598641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360065516324185966131521 270049137243139474598641)
            ·
              refine ⟨202536852932354605948981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270049137243139474598641 202536852932354605948981)
              ·
                refine ⟨18987829962408244307717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202536852932354605948981 18987829962408244307717)
                ·
                  rfl

theorem cell21_249606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_249606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249606 prefixEnd_249606 := by exact prefixLift 249606
  have htrace : WordTrace (prefixWord ++ tailWord_249606) baseStart_249606 baseEnd_249606 := by
    simpa [prefixWord, tailWord_249606, baseEnd_249606] using wordTrace_append hprefix tailTrace_249606
  have hstable : (prefixWord ++ tailWord_249606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249606).length < 2 ^ (prefixWord ++ tailWord_249606).sum := by decide
  have hdescent : baseEnd_249606 < baseStart_249606 := by decide
  rcases family_descends (prefixWord ++ tailWord_249606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249620 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_249620 : Nat := 118140960795 + 249620 * 2 ^ 59
def prefixEnd_249620 : Nat := 4983230072969 + 3 ^ 40 * 249620 * 2
def baseEnd_249620 : Nat := 56966684877963819689789

theorem tailTrace_249620 : CollatzResearch.WordTrace tailWord_249620 prefixEnd_249620 56966684877963819689789 := by
  unfold tailWord_249620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552194677838423273513157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6069592903784564364684209 4552194677838423273513157)
  ·
    refine ⟨853536502094704363783717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4552194677838423273513157 853536502094704363783717)
    ·
      refine ⟨160038094142757068209447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 853536502094704363783717 160038094142757068209447)
      ·
        refine ⟨240057141214135602314171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160038094142757068209447 240057141214135602314171)
        ·
          refine ⟨360085711821203403471257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240057141214135602314171 360085711821203403471257)
          ·
            refine ⟨270064283865902552603443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360085711821203403471257 270064283865902552603443)
            ·
              refine ⟨405096425798853828905165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270064283865902552603443 405096425798853828905165)
              ·
                refine ⟨151911159674570185839437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405096425798853828905165 151911159674570185839437)
                ·
                  refine ⟨56966684877963819689789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151911159674570185839437 56966684877963819689789)
                  ·
                    rfl

theorem cell21_249620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_249620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249620 prefixEnd_249620 := by exact prefixLift 249620
  have htrace : WordTrace (prefixWord ++ tailWord_249620) baseStart_249620 baseEnd_249620 := by
    simpa [prefixWord, tailWord_249620, baseEnd_249620] using wordTrace_append hprefix tailTrace_249620
  have hstable : (prefixWord ++ tailWord_249620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249620).length < 2 ^ (prefixWord ++ tailWord_249620).sum := by decide
  have hdescent : baseEnd_249620 < baseStart_249620 := by decide
  rcases family_descends (prefixWord ++ tailWord_249620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249656 : List Nat := [2, 1, 2, 1, 3, 4, 2, 6]
def baseStart_249656 : Nat := 118140960795 + 249656 * 2 ^ 59
def prefixEnd_249656 : Nat := 4983230072969 + 3 ^ 40 * 249656 * 2
def baseEnd_249656 : Nat := 18991633522811919029905

theorem tailTrace_249656 : CollatzResearch.WordTrace tailWord_249656 prefixEnd_249656 18991633522811919029905 := by
  unfold tailWord_249656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552851191773212347668411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6070468255697616463557881 4552851191773212347668411)
  ·
    refine ⟨6829276787659818521502617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552851191773212347668411 6829276787659818521502617)
    ·
      refine ⟨5121957590744863891126963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6829276787659818521502617 5121957590744863891126963)
      ·
        refine ⟨7682936386117295836690445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121957590744863891126963 7682936386117295836690445)
        ·
          refine ⟨2881101144793985938758917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7682936386117295836690445 2881101144793985938758917)
          ·
            refine ⟨540206464648872363517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2881101144793985938758917 540206464648872363517297)
            ·
              refine ⟨405154848486654272637973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540206464648872363517297 405154848486654272637973)
              ·
                refine ⟨18991633522811919029905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405154848486654272637973 18991633522811919029905)
                ·
                  rfl

theorem cell21_249656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_249656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249656 prefixEnd_249656 := by exact prefixLift 249656
  have htrace : WordTrace (prefixWord ++ tailWord_249656) baseStart_249656 baseEnd_249656 := by
    simpa [prefixWord, tailWord_249656, baseEnd_249656] using wordTrace_append hprefix tailTrace_249656
  have hstable : (prefixWord ++ tailWord_249656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249656).length < 2 ^ (prefixWord ++ tailWord_249656).sum := by decide
  have hdescent : baseEnd_249656 < baseStart_249656 := by decide
  rcases family_descends (prefixWord ++ tailWord_249656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249704 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_249704 : Nat := 118140960795 + 249704 * 2 ^ 59
def prefixEnd_249704 : Nat := 4983230072969 + 3 ^ 40 * 249704 * 2
def baseEnd_249704 : Nat := 56985854822398340289617

theorem tailTrace_249704 : CollatzResearch.WordTrace tailWord_249704 prefixEnd_249704 56985854822398340289617 := by
  unfold tailWord_249704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553726543686264446542083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6071635391581685928722777 4553726543686264446542083)
  ·
    refine ⟨6830589815529396669813125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553726543686264446542083 6830589815529396669813125)
    ·
      refine ⟨1280735590411761875589961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6830589815529396669813125 1280735590411761875589961)
      ·
        refine ⟨960551692808821406692471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280735590411761875589961 960551692808821406692471)
        ·
          refine ⟨1440827539213232110038707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960551692808821406692471 1440827539213232110038707)
          ·
            refine ⟨2161241308819848165058061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440827539213232110038707 2161241308819848165058061)
            ·
              refine ⟨810465490807443061896773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2161241308819848165058061 810465490807443061896773)
              ·
                refine ⟨151962279526395574105645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810465490807443061896773 151962279526395574105645)
                ·
                  refine ⟨56985854822398340289617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151962279526395574105645 56985854822398340289617)
                  ·
                    rfl

theorem cell21_249704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_249704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249704 prefixEnd_249704 := by exact prefixLift 249704
  have htrace : WordTrace (prefixWord ++ tailWord_249704) baseStart_249704 baseEnd_249704 := by
    simpa [prefixWord, tailWord_249704, baseEnd_249704] using wordTrace_append hprefix tailTrace_249704
  have hstable : (prefixWord ++ tailWord_249704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249704).length < 2 ^ (prefixWord ++ tailWord_249704).sum := by decide
  have hdescent : baseEnd_249704 < baseStart_249704 := by decide
  rcases family_descends (prefixWord ++ tailWord_249704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249752 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_249752 : Nat := 118140960795 + 249752 * 2 ^ 59
def prefixEnd_249752 : Nat := 4983230072969 + 3 ^ 40 * 249752 * 2
def baseEnd_249752 : Nat := 56996809076360923489519

theorem tailTrace_249752 : CollatzResearch.WordTrace tailWord_249752 prefixEnd_249752 56996809076360923489519 := by
  unfold tailWord_249752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554601895599316545415755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6072802527465755393887673 4554601895599316545415755)
  ·
    refine ⟨6831902843398974818123633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4554601895599316545415755 6831902843398974818123633)
    ·
      refine ⟨5123927132549231113592725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6831902843398974818123633 5123927132549231113592725)
      ·
        refine ⟨240184084338245208449659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5123927132549231113592725 240184084338245208449659)
        ·
          refine ⟨360276126507367812674489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240184084338245208449659 360276126507367812674489)
          ·
            refine ⟨270207094880525859505867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360276126507367812674489 270207094880525859505867)
            ·
              refine ⟨405310642320788789258801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270207094880525859505867 405310642320788789258801)
              ·
                refine ⟨303982981740591591944101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405310642320788789258801 303982981740591591944101)
                ·
                  refine ⟨56996809076360923489519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303982981740591591944101 56996809076360923489519)
                  ·
                    rfl

theorem cell21_249752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_249752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249752 prefixEnd_249752 := by exact prefixLift 249752
  have htrace : WordTrace (prefixWord ++ tailWord_249752) baseStart_249752 baseEnd_249752 := by
    simpa [prefixWord, tailWord_249752, baseEnd_249752] using wordTrace_append hprefix tailTrace_249752
  have hstable : (prefixWord ++ tailWord_249752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249752).length < 2 ^ (prefixWord ++ tailWord_249752).sum := by decide
  have hdescent : baseEnd_249752 < baseStart_249752 := by decide
  rcases family_descends (prefixWord ++ tailWord_249752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249791 : List Nat := [1, 1, 2, 2, 2, 1, 5, 7]
def baseStart_249791 : Nat := 118140960795 + 249791 * 2 ^ 59
def prefixEnd_249791 : Nat := 4983230072969 + 3 ^ 40 * 249791 * 2
def baseEnd_249791 : Nat := 19001903135901840779813

theorem tailTrace_249791 : CollatzResearch.WordTrace tailWord_249791 prefixEnd_249791 19001903135901840779813 := by
  unfold tailWord_249791
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110626238057342751501227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6073750825371561834334151 9110626238057342751501227)
  ·
    refine ⟨13665939357086014127251841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110626238057342751501227 13665939357086014127251841)
    ·
      refine ⟨10249454517814510595438881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13665939357086014127251841 10249454517814510595438881)
      ·
        refine ⟨7687090888360882946579161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10249454517814510595438881 7687090888360882946579161)
        ·
          refine ⟨5765318166270662209934371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7687090888360882946579161 5765318166270662209934371)
          ·
            refine ⟨8647977249405993314901557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765318166270662209934371 8647977249405993314901557)
            ·
              refine ⟨810747867131811873272021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8647977249405993314901557 810747867131811873272021)
              ·
                refine ⟨19001903135901840779813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 810747867131811873272021 19001903135901840779813)
                ·
                  rfl

theorem cell21_249791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_249791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249791 prefixEnd_249791 := by exact prefixLift 249791
  have htrace : WordTrace (prefixWord ++ tailWord_249791) baseStart_249791 baseEnd_249791 := by
    simpa [prefixWord, tailWord_249791, baseEnd_249791] using wordTrace_append hprefix tailTrace_249791
  have hstable : (prefixWord ++ tailWord_249791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249791).length < 2 ^ (prefixWord ++ tailWord_249791).sum := by decide
  have hdescent : baseEnd_249791 < baseStart_249791 := by decide
  rcases family_descends (prefixWord ++ tailWord_249791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249814 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_249814 : Nat := 118140960795 + 249814 * 2 ^ 59
def prefixEnd_249814 : Nat := 4983230072969 + 3 ^ 40 * 249814 * 2
def baseEnd_249814 : Nat := 57010958321062593456059

theorem tailTrace_249814 : CollatzResearch.WordTrace tailWord_249814 prefixEnd_249814 57010958321062593456059 := by
  unfold tailWord_249814
  simp only [CollatzResearch.WordTrace]
  refine ⟨569466569810876104974281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6074310077982678453058997 569466569810876104974281)
  ·
    refine ⟨427099927358157078730711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 569466569810876104974281 427099927358157078730711)
    ·
      refine ⟨640649891037235618096067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427099927358157078730711 640649891037235618096067)
      ·
        refine ⟨960974836555853427144101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640649891037235618096067 960974836555853427144101)
        ·
          refine ⟨180182781854222517589519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 960974836555853427144101 180182781854222517589519)
          ·
            refine ⟨270274172781333776384279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180182781854222517589519 270274172781333776384279)
            ·
              refine ⟨405411259172000664576419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270274172781333776384279 405411259172000664576419)
              ·
                refine ⟨608116888758000996864629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405411259172000664576419 608116888758000996864629)
                ·
                  refine ⟨57010958321062593456059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 608116888758000996864629 57010958321062593456059)
                  ·
                    rfl

theorem cell21_249814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_249814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249814 prefixEnd_249814 := by exact prefixLift 249814
  have htrace : WordTrace (prefixWord ++ tailWord_249814) baseStart_249814 baseEnd_249814 := by
    simpa [prefixWord, tailWord_249814, baseEnd_249814] using wordTrace_append hprefix tailTrace_249814
  have hstable : (prefixWord ++ tailWord_249814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249814).length < 2 ^ (prefixWord ++ tailWord_249814).sum := by decide
  have hdescent : baseEnd_249814 < baseStart_249814 := by decide
  rcases family_descends (prefixWord ++ tailWord_249814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249862 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_249862 : Nat := 118140960795 + 249862 * 2 ^ 59
def prefixEnd_249862 : Nat := 4983230072969 + 3 ^ 40 * 249862 * 2
def baseEnd_249862 : Nat := 57021912575025176655961

theorem tailTrace_249862 : CollatzResearch.WordTrace tailWord_249862 prefixEnd_249862 57021912575025176655961 := by
  unfold tailWord_249862
  simp only [CollatzResearch.WordTrace]
  refine ⟨284787994400003808666745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6075477213866747918223893 284787994400003808666745)
  ·
    refine ⟨213590995800002856500059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284787994400003808666745 213590995800002856500059)
    ·
      refine ⟨320386493700004284750089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213590995800002856500059 320386493700004284750089)
      ·
        refine ⟨240289870275003213562567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320386493700004284750089 240289870275003213562567)
        ·
          refine ⟨360434805412504820343851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240289870275003213562567 360434805412504820343851)
          ·
            refine ⟨540652208118757230515777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360434805412504820343851 540652208118757230515777)
            ·
              refine ⟨405489156089067922886833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540652208118757230515777 405489156089067922886833)
              ·
                refine ⟨304116867066800942165125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405489156089067922886833 304116867066800942165125)
                ·
                  refine ⟨57021912575025176655961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304116867066800942165125 57021912575025176655961)
                  ·
                    rfl

theorem cell21_249862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_249862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249862 prefixEnd_249862 := by exact prefixLift 249862
  have htrace : WordTrace (prefixWord ++ tailWord_249862) baseStart_249862 baseEnd_249862 := by
    simpa [prefixWord, tailWord_249862, baseEnd_249862] using wordTrace_append hprefix tailTrace_249862
  have hstable : (prefixWord ++ tailWord_249862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249862).length < 2 ^ (prefixWord ++ tailWord_249862).sum := by decide
  have hdescent : baseEnd_249862 < baseStart_249862 := by decide
  rcases family_descends (prefixWord ++ tailWord_249862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249870 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_249870 : Nat := 118140960795 + 249870 * 2 ^ 59
def prefixEnd_249870 : Nat := 4983230072969 + 3 ^ 40 * 249870 * 2
def baseEnd_249870 : Nat := 57023738284018940522611

theorem tailTrace_249870 : CollatzResearch.WordTrace tailWord_249870 prefixEnd_249870 57023738284018940522611 := by
  unfold tailWord_249870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139188450596392405453383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6075671736514092829084709 1139188450596392405453383)
  ·
    refine ⟨1708782675894588608180075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139188450596392405453383 1708782675894588608180075)
    ·
      refine ⟨2563174013841882912270113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708782675894588608180075 2563174013841882912270113)
      ·
        refine ⟨1922380510381412184202585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2563174013841882912270113 1922380510381412184202585)
        ·
          refine ⟨1441785382786059138151939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922380510381412184202585 1441785382786059138151939)
          ·
            refine ⟨2162678074179088707227909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441785382786059138151939 2162678074179088707227909)
            ·
              refine ⟨405502138908579132605233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2162678074179088707227909 405502138908579132605233)
              ·
                refine ⟨304126604181434349453925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405502138908579132605233 304126604181434349453925)
                ·
                  refine ⟨57023738284018940522611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304126604181434349453925 57023738284018940522611)
                  ·
                    rfl

theorem cell21_249870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_249870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249870 prefixEnd_249870 := by exact prefixLift 249870
  have htrace : WordTrace (prefixWord ++ tailWord_249870) baseStart_249870 baseEnd_249870 := by
    simpa [prefixWord, tailWord_249870, baseEnd_249870] using wordTrace_append hprefix tailTrace_249870
  have hstable : (prefixWord ++ tailWord_249870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249870).length < 2 ^ (prefixWord ++ tailWord_249870).sum := by decide
  have hdescent : baseEnd_249870 < baseStart_249870 := by decide
  rcases family_descends (prefixWord ++ tailWord_249870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249884 : List Nat := [2, 2, 3, 1, 3, 1, 3, 6]
def baseStart_249884 : Nat := 118140960795 + 249884 * 2 ^ 59
def prefixEnd_249884 : Nat := 4983230072969 + 3 ^ 40 * 249884 * 2
def baseEnd_249884 : Nat := 19008977758252675763083

theorem tailTrace_249884 : CollatzResearch.WordTrace tailWord_249884 prefixEnd_249884 19008977758252675763083 := by
  unfold tailWord_249884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557009113360209817318353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6076012151146946423091137 4557009113360209817318353)
  ·
    refine ⟨3417756835020157362988765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4557009113360209817318353 3417756835020157362988765)
    ·
      refine ⟨1281658813132559011120787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3417756835020157362988765 1281658813132559011120787)
      ·
        refine ⟨1922488219698838516681181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281658813132559011120787 1922488219698838516681181)
        ·
          refine ⟨720933082387064443755443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1922488219698838516681181 720933082387064443755443)
          ·
            refine ⟨1081399623580596665633165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720933082387064443755443 1081399623580596665633165)
            ·
              refine ⟨405524858842723749612437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1081399623580596665633165 405524858842723749612437)
              ·
                refine ⟨19008977758252675763083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405524858842723749612437 19008977758252675763083)
                ·
                  rfl

theorem cell21_249884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_249884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249884 prefixEnd_249884 := by exact prefixLift 249884
  have htrace : WordTrace (prefixWord ++ tailWord_249884) baseStart_249884 baseEnd_249884 := by
    simpa [prefixWord, tailWord_249884, baseEnd_249884] using wordTrace_append hprefix tailTrace_249884
  have hstable : (prefixWord ++ tailWord_249884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249884).length < 2 ^ (prefixWord ++ tailWord_249884).sum := by decide
  have hdescent : baseEnd_249884 < baseStart_249884 := by decide
  rcases family_descends (prefixWord ++ tailWord_249884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249946 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_249946 : Nat := 118140960795 + 249946 * 2 ^ 59
def prefixEnd_249946 : Nat := 4983230072969 + 3 ^ 40 * 249946 * 2
def baseEnd_249946 : Nat := 57041082519459697255789

theorem tailTrace_249946 : CollatzResearch.WordTrace tailWord_249946 prefixEnd_249946 57041082519459697255789 := by
  unfold tailWord_249946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279069888123951055848423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6077519701663869482262461 2279069888123951055848423)
  ·
    refine ⟨3418604832185926583772635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2279069888123951055848423 3418604832185926583772635)
    ·
      refine ⟨5127907248278889875658953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418604832185926583772635 5127907248278889875658953)
      ·
        refine ⟨3845930436209167406744215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5127907248278889875658953 3845930436209167406744215)
        ·
          refine ⟨5768895654313751110116323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845930436209167406744215 5768895654313751110116323)
          ·
            refine ⟨8653343481470626665174485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768895654313751110116323 8653343481470626665174485)
            ·
              refine ⟨202812737846967812465027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8653343481470626665174485 202812737846967812465027)
              ·
                refine ⟨304219106770451718697541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202812737846967812465027 304219106770451718697541)
                ·
                  refine ⟨57041082519459697255789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304219106770451718697541 57041082519459697255789)
                  ·
                    rfl

theorem cell21_249946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_249946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249946 prefixEnd_249946 := by exact prefixLift 249946
  have htrace : WordTrace (prefixWord ++ tailWord_249946) baseStart_249946 baseEnd_249946 := by
    simpa [prefixWord, tailWord_249946, baseEnd_249946] using wordTrace_append hprefix tailTrace_249946
  have hstable : (prefixWord ++ tailWord_249946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249946).length < 2 ^ (prefixWord ++ tailWord_249946).sum := by decide
  have hdescent : baseEnd_249946 < baseStart_249946 := by decide
  rcases family_descends (prefixWord ++ tailWord_249946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249991 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 3]
def baseStart_249991 : Nat := 118140960795 + 249991 * 2 ^ 59
def prefixEnd_249991 : Nat := 4983230072969 + 3 ^ 40 * 249991 * 2
def baseEnd_249991 : Nat := 57051352132549619005697

theorem tailTrace_249991 : CollatzResearch.WordTrace tailWord_249991 prefixEnd_249991 57051352132549619005697 := by
  unfold tailWord_249991
  simp only [CollatzResearch.WordTrace]
  refine ⟨9117920837332776908781827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6078613891555184605854551 9117920837332776908781827)
  ·
    refine ⟨13676881255999165363172741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9117920837332776908781827 13676881255999165363172741)
    ·
      refine ⟨2564415235499843505594889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13676881255999165363172741 2564415235499843505594889)
      ·
        refine ⟨1923311426624882629196167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2564415235499843505594889 1923311426624882629196167)
        ·
          refine ⟨2884967139937323943794251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923311426624882629196167 2884967139937323943794251)
          ·
            refine ⟨4327450709905985915691377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884967139937323943794251 4327450709905985915691377)
            ·
              refine ⟨3245588032429489436768533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4327450709905985915691377 3245588032429489436768533)
              ·
                refine ⟨152136939020132317348525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3245588032429489436768533 152136939020132317348525)
                ·
                  refine ⟨57051352132549619005697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152136939020132317348525 57051352132549619005697)
                  ·
                    rfl

theorem cell21_249991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 3].length) (baseStart_249991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_249991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_249991 prefixEnd_249991 := by exact prefixLift 249991
  have htrace : WordTrace (prefixWord ++ tailWord_249991) baseStart_249991 baseEnd_249991 := by
    simpa [prefixWord, tailWord_249991, baseEnd_249991] using wordTrace_append hprefix tailTrace_249991
  have hstable : (prefixWord ++ tailWord_249991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249991).length < 2 ^ (prefixWord ++ tailWord_249991).sum := by decide
  have hdescent : baseEnd_249991 < baseStart_249991 := by decide
  rcases family_descends (prefixWord ++ tailWord_249991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250005 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_250005 : Nat := 118140960795 + 250005 * 2 ^ 59
def prefixEnd_250005 : Nat := 4983230072969 + 3 ^ 40 * 250005 * 2
def baseEnd_250005 : Nat := 57054547123288705772335

theorem tailTrace_250005 : CollatzResearch.WordTrace tailWord_250005 prefixEnd_250005 57054547123288705772335 := by
  unfold tailWord_250005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118431459282057299791469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6078954306188038199860979 9118431459282057299791469)
  ·
    refine ⟨3419411797230771487421801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9118431459282057299791469 3419411797230771487421801)
    ·
      refine ⟨2564558847923078615566351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3419411797230771487421801 2564558847923078615566351)
      ·
        refine ⟨3846838271884617923349527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564558847923078615566351 3846838271884617923349527)
        ·
          refine ⟨5770257407826926885024291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846838271884617923349527 5770257407826926885024291)
          ·
            refine ⟨8655386111740390327536437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770257407826926885024291 8655386111740390327536437)
            ·
              refine ⟨811442447975661593206541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8655386111740390327536437 811442447975661593206541)
              ·
                refine ⟨304290917990873097452453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811442447975661593206541 304290917990873097452453)
                ·
                  refine ⟨57054547123288705772335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304290917990873097452453 57054547123288705772335)
                  ·
                    rfl

theorem cell21_250005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_250005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250005 prefixEnd_250005 := by exact prefixLift 250005
  have htrace : WordTrace (prefixWord ++ tailWord_250005) baseStart_250005 baseEnd_250005 := by
    simpa [prefixWord, tailWord_250005, baseEnd_250005] using wordTrace_append hprefix tailTrace_250005
  have hstable : (prefixWord ++ tailWord_250005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250005).length < 2 ^ (prefixWord ++ tailWord_250005).sum := by decide
  have hdescent : baseEnd_250005 < baseStart_250005 := by decide
  rcases family_descends (prefixWord ++ tailWord_250005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250070 : List Nat := [5, 2, 1, 2, 1, 2, 3, 5]
def baseStart_250070 : Nat := 118140960795 + 250070 * 2 ^ 59
def prefixEnd_250070 : Nat := 4983230072969 + 3 ^ 40 * 250070 * 2
def baseEnd_250070 : Nat := 19023127002954345729623

theorem tailTrace_250070 : CollatzResearch.WordTrace tailWord_250070 prefixEnd_250070 19023127002954345729623 := by
  unfold tailWord_250070
  simp only [CollatzResearch.WordTrace]
  refine ⟨570050137752910837556729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6080534802697715600605109 570050137752910837556729)
  ·
    refine ⟨427537603314683128167547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 570050137752910837556729 427537603314683128167547)
    ·
      refine ⟨641306404972024692251321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427537603314683128167547 641306404972024692251321)
      ·
        refine ⟨480979803729018519188491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641306404972024692251321 480979803729018519188491)
        ·
          refine ⟨721469705593527778782737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480979803729018519188491 721469705593527778782737)
          ·
            refine ⟨541102279195145834087053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721469705593527778782737 541102279195145834087053)
            ·
              refine ⟨202913354698179687782645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541102279195145834087053 202913354698179687782645)
              ·
                refine ⟨19023127002954345729623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202913354698179687782645 19023127002954345729623)
                ·
                  rfl

theorem cell21_250070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_250070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250070 prefixEnd_250070 := by exact prefixLift 250070
  have htrace : WordTrace (prefixWord ++ tailWord_250070) baseStart_250070 baseEnd_250070 := by
    simpa [prefixWord, tailWord_250070, baseEnd_250070] using wordTrace_append hprefix tailTrace_250070
  have hstable : (prefixWord ++ tailWord_250070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250070).length < 2 ^ (prefixWord ++ tailWord_250070).sum := by decide
  have hdescent : baseEnd_250070 < baseStart_250070 := by decide
  rcases family_descends (prefixWord ++ tailWord_250070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250095 : List Nat := [1, 1, 2, 1, 6, 2, 8]
def baseStart_250095 : Nat := 118140960795 + 250095 * 2 ^ 59
def prefixEnd_250095 : Nat := 4983230072969 + 3 ^ 40 * 250095 * 2
def baseEnd_250095 : Nat := 6341676261052061030239

theorem tailTrace_250095 : CollatzResearch.WordTrace tailWord_250095 prefixEnd_250095 6341676261052061030239 := by
  unfold tailWord_250095
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121714028956002670567739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6081142685970668447045159 9121714028956002670567739)
  ·
    refine ⟨13682571043434004005851609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9121714028956002670567739 13682571043434004005851609)
    ·
      refine ⟨10261928282575503004388707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13682571043434004005851609 10261928282575503004388707)
      ·
        refine ⟨15392892423863254506583061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261928282575503004388707 15392892423863254506583061)
        ·
          refine ⟨721541832368590054996081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15392892423863254506583061 721541832368590054996081)
          ·
            refine ⟨541156374276442541247061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721541832368590054996081 541156374276442541247061)
            ·
              refine ⟨6341676261052061030239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 541156374276442541247061 6341676261052061030239)
              ·
                rfl

theorem cell21_250095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 8].length) (baseStart_250095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250095 prefixEnd_250095 := by exact prefixLift 250095
  have htrace : WordTrace (prefixWord ++ tailWord_250095) baseStart_250095 baseEnd_250095 := by
    simpa [prefixWord, tailWord_250095, baseEnd_250095] using wordTrace_append hprefix tailTrace_250095
  have hstable : (prefixWord ++ tailWord_250095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250095).length < 2 ^ (prefixWord ++ tailWord_250095).sum := by decide
  have hdescent : baseEnd_250095 < baseStart_250095 := by decide
  rcases family_descends (prefixWord ++ tailWord_250095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250098 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_250098 : Nat := 118140960795 + 250098 * 2 ^ 59
def prefixEnd_250098 : Nat := 4983230072969 + 3 ^ 40 * 250098 * 2
def baseEnd_250098 : Nat := 57075770990341210722145

theorem tailTrace_250098 : CollatzResearch.WordTrace tailWord_250098 prefixEnd_250098 57075770990341210722145 := by
  unfold tailWord_250098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280455861986283545731737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6081215631963422788617965 2280455861986283545731737)
  ·
    refine ⟨1710341896489712659298803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2280455861986283545731737 1710341896489712659298803)
    ·
      refine ⟨2565512844734568988948205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710341896489712659298803 2565512844734568988948205)
      ·
        refine ⟨962067316775463370855577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2565512844734568988948205 962067316775463370855577)
        ·
          refine ⟨721550487581597528141683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962067316775463370855577 721550487581597528141683)
          ·
            refine ⟨1082325731372396292212525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721550487581597528141683 1082325731372396292212525)
            ·
              refine ⟨405872149264648609579697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1082325731372396292212525 405872149264648609579697)
              ·
                refine ⟨304404111948486457184773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405872149264648609579697 304404111948486457184773)
                ·
                  refine ⟨57075770990341210722145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304404111948486457184773 57075770990341210722145)
                  ·
                    rfl

theorem cell21_250098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_250098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250098 prefixEnd_250098 := by exact prefixLift 250098
  have htrace : WordTrace (prefixWord ++ tailWord_250098) baseStart_250098 baseEnd_250098 := by
    simpa [prefixWord, tailWord_250098, baseEnd_250098] using wordTrace_append hprefix tailTrace_250098
  have hstable : (prefixWord ++ tailWord_250098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250098).length < 2 ^ (prefixWord ++ tailWord_250098).sum := by decide
  have hdescent : baseEnd_250098 < baseStart_250098 := by decide
  rcases family_descends (prefixWord ++ tailWord_250098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250126 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_250126 : Nat := 118140960795 + 250126 * 2 ^ 59
def prefixEnd_250126 : Nat := 4983230072969 + 3 ^ 40 * 250126 * 2
def baseEnd_250126 : Nat := 57082160971819384255421

theorem tailTrace_250126 : CollatzResearch.WordTrace tailWord_250126 prefixEnd_250126 57082160971819384255421 := by
  unfold tailWord_250126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140355586480461870618279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6081896461229129976630821 1140355586480461870618279)
  ·
    refine ⟨1710533379720692805927419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1140355586480461870618279 1710533379720692805927419)
    ·
      refine ⟨2565800069581039208891129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710533379720692805927419 2565800069581039208891129)
      ·
        refine ⟨1924350052185779406668347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2565800069581039208891129 1924350052185779406668347)
        ·
          refine ⟨2886525078278669110002521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924350052185779406668347 2886525078278669110002521)
          ·
            refine ⟨2164893808709001832501891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886525078278669110002521 2164893808709001832501891)
            ·
              refine ⟨3247340713063502748752837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164893808709001832501891 3247340713063502748752837)
              ·
                refine ⟨608876383699406765391157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3247340713063502748752837 608876383699406765391157)
                ·
                  refine ⟨57082160971819384255421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 608876383699406765391157 57082160971819384255421)
                  ·
                    rfl

theorem cell21_250126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_250126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250126 prefixEnd_250126 := by exact prefixLift 250126
  have htrace : WordTrace (prefixWord ++ tailWord_250126) baseStart_250126 baseEnd_250126 := by
    simpa [prefixWord, tailWord_250126, baseEnd_250126] using wordTrace_append hprefix tailTrace_250126
  have hstable : (prefixWord ++ tailWord_250126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250126).length < 2 ^ (prefixWord ++ tailWord_250126).sum := by decide
  have hdescent : baseEnd_250126 < baseStart_250126 := by decide
  rcases family_descends (prefixWord ++ tailWord_250126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250174 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_250174 : Nat := 118140960795 + 250174 * 2 ^ 59
def prefixEnd_250174 : Nat := 4983230072969 + 3 ^ 40 * 250174 * 2
def baseEnd_250174 : Nat := 57093115225781967455323

theorem tailTrace_250174 : CollatzResearch.WordTrace tailWord_250174 prefixEnd_250174 57093115225781967455323 := by
  unfold tailWord_250174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140574424458724895336697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6083063597113199441795717 1140574424458724895336697)
  ·
    refine ⟨855430818344043671502523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1140574424458724895336697 855430818344043671502523)
    ·
      refine ⟨1283146227516065507253785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855430818344043671502523 1283146227516065507253785)
      ·
        refine ⟨962359670637049130440339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1283146227516065507253785 962359670637049130440339)
        ·
          refine ⟨1443539505955573695660509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962359670637049130440339 1443539505955573695660509)
          ·
            refine ⟨541327314733340135872691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1443539505955573695660509 541327314733340135872691)
            ·
              refine ⟨811990972100010203809037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541327314733340135872691 811990972100010203809037)
              ·
                refine ⟨304496614537503826428389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811990972100010203809037 304496614537503826428389)
                ·
                  refine ⟨57093115225781967455323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304496614537503826428389 57093115225781967455323)
                  ·
                    rfl

theorem cell21_250174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_250174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250174 prefixEnd_250174 := by exact prefixLift 250174
  have htrace : WordTrace (prefixWord ++ tailWord_250174) baseStart_250174 baseEnd_250174 := by
    simpa [prefixWord, tailWord_250174, baseEnd_250174] using wordTrace_append hprefix tailTrace_250174
  have hstable : (prefixWord ++ tailWord_250174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250174).length < 2 ^ (prefixWord ++ tailWord_250174).sum := by decide
  have hdescent : baseEnd_250174 < baseStart_250174 := by decide
  rcases family_descends (prefixWord ++ tailWord_250174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250185 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_250185 : Nat := 118140960795 + 250185 * 2 ^ 59
def prefixEnd_250185 : Nat := 4983230072969 + 3 ^ 40 * 250185 * 2
def baseEnd_250185 : Nat := 57095625575648392771967

theorem tailTrace_250185 : CollatzResearch.WordTrace tailWord_250185 prefixEnd_250185 57095625575648392771967 := by
  unfold tailWord_250185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124996598629948041344009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6083331065753298694229339 9124996598629948041344009)
  ·
    refine ⟨6843747448972461031008007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9124996598629948041344009 6843747448972461031008007)
    ·
      refine ⟨10265621173458691546512011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843747448972461031008007 10265621173458691546512011)
      ·
        refine ⟨15398431760188037319768017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10265621173458691546512011 15398431760188037319768017)
        ·
          refine ⟨11548823820141027989826013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15398431760188037319768017 11548823820141027989826013)
          ·
            refine ⟨4330808932552885496184755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11548823820141027989826013 4330808932552885496184755)
            ·
              refine ⟨6496213398829328244277133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330808932552885496184755 6496213398829328244277133)
              ·
                refine ⟨2436080024560998091603925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6496213398829328244277133 2436080024560998091603925)
                ·
                  refine ⟨57095625575648392771967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2436080024560998091603925 57095625575648392771967)
                  ·
                    rfl

theorem cell21_250185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_250185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250185 prefixEnd_250185 := by exact prefixLift 250185
  have htrace : WordTrace (prefixWord ++ tailWord_250185) baseStart_250185 baseEnd_250185 := by
    simpa [prefixWord, tailWord_250185, baseEnd_250185] using wordTrace_append hprefix tailTrace_250185
  have hstable : (prefixWord ++ tailWord_250185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250185).length < 2 ^ (prefixWord ++ tailWord_250185).sum := by decide
  have hdescent : baseEnd_250185 < baseStart_250185 := by decide
  rcases family_descends (prefixWord ++ tailWord_250185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250261 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_250261 : Nat := 118140960795 + 250261 * 2 ^ 59
def prefixEnd_250261 : Nat := 4983230072969 + 3 ^ 40 * 250261 * 2
def baseEnd_250261 : Nat := 57112969811089149505145

theorem tailTrace_250261 : CollatzResearch.WordTrace tailWord_250261 prefixEnd_250261 57112969811089149505145 := by
  unfold tailWord_250261
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127768546354613021110637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6085179030903075347407091 9127768546354613021110637)
  ·
    refine ⟨3422913204882979882916489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9127768546354613021110637 3422913204882979882916489)
    ·
      refine ⟨2567184903662234912187367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3422913204882979882916489 2567184903662234912187367)
      ·
        refine ⟨3850777355493352368281051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567184903662234912187367 3850777355493352368281051)
        ·
          refine ⟨5776166033240028552421577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850777355493352368281051 5776166033240028552421577)
          ·
            refine ⟨4332124524930021414316183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776166033240028552421577 4332124524930021414316183)
            ·
              refine ⟨6498186787395032121474275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332124524930021414316183 6498186787395032121474275)
              ·
                refine ⟨9747280181092548182211413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498186787395032121474275 9747280181092548182211413)
                ·
                  refine ⟨57112969811089149505145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9747280181092548182211413 57112969811089149505145)
                  ·
                    rfl

theorem cell21_250261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_250261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250261 prefixEnd_250261 := by exact prefixLift 250261
  have htrace : WordTrace (prefixWord ++ tailWord_250261) baseStart_250261 baseEnd_250261 := by
    simpa [prefixWord, tailWord_250261, baseEnd_250261] using wordTrace_append hprefix tailTrace_250261
  have hstable : (prefixWord ++ tailWord_250261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250261).length < 2 ^ (prefixWord ++ tailWord_250261).sum := by decide
  have hdescent : baseEnd_250261 < baseStart_250261 := by decide
  rcases family_descends (prefixWord ++ tailWord_250261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250312 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_250312 : Nat := 118140960795 + 250312 * 2 ^ 59
def prefixEnd_250312 : Nat := 4983230072969 + 3 ^ 40 * 250312 * 2
def baseEnd_250312 : Nat := 57124608705924394155041

theorem tailTrace_250312 : CollatzResearch.WordTrace tailWord_250312 prefixEnd_250312 57124608705924394155041 := by
  unfold tailWord_250312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564814334584924365608595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6086419112779899154144793 4564814334584924365608595)
  ·
    refine ⟨6847221501877386548412893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4564814334584924365608595 6847221501877386548412893)
    ·
      refine ⟨2567708063204019955654835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6847221501877386548412893 2567708063204019955654835)
      ·
        refine ⟨3851562094806029933482253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567708063204019955654835 3851562094806029933482253)
        ·
          refine ⟨1444335785552261225055845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3851562094806029933482253 1444335785552261225055845)
          ·
            refine ⟨270812959791048979697971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1444335785552261225055845 270812959791048979697971)
            ·
              refine ⟨406219439686573469546957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270812959791048979697971 406219439686573469546957)
              ·
                refine ⟨152332289882465051080109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406219439686573469546957 152332289882465051080109)
                ·
                  refine ⟨57124608705924394155041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152332289882465051080109 57124608705924394155041)
                  ·
                    rfl

theorem cell21_250312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_250312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250312 prefixEnd_250312 := by exact prefixLift 250312
  have htrace : WordTrace (prefixWord ++ tailWord_250312) baseStart_250312 baseEnd_250312 := by
    simpa [prefixWord, tailWord_250312, baseEnd_250312] using wordTrace_append hprefix tailTrace_250312
  have hstable : (prefixWord ++ tailWord_250312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250312).length < 2 ^ (prefixWord ++ tailWord_250312).sum := by decide
  have hdescent : baseEnd_250312 < baseStart_250312 := by decide
  rcases family_descends (prefixWord ++ tailWord_250312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250326 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_250326 : Nat := 118140960795 + 250326 * 2 ^ 59
def prefixEnd_250326 : Nat := 4983230072969 + 3 ^ 40 * 250326 * 2
def baseEnd_250326 : Nat := 57127803696663480921679

theorem tailTrace_250326 : CollatzResearch.WordTrace tailWord_250326 prefixEnd_250326 57127803696663480921679 := by
  unfold tailWord_250326
  simp only [CollatzResearch.WordTrace]
  refine ⟨570633705694945570139177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6086759527412752748151221 570633705694945570139177)
  ·
    refine ⟨427975279271209177604383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 570633705694945570139177 427975279271209177604383)
    ·
      refine ⟨641962918906813766406575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427975279271209177604383 641962918906813766406575)
      ·
        refine ⟨962944378360220649609863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641962918906813766406575 962944378360220649609863)
        ·
          refine ⟨1444416567540330974414795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962944378360220649609863 1444416567540330974414795)
          ·
            refine ⟨2166624851310496461622193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444416567540330974414795 2166624851310496461622193)
            ·
              refine ⟨1624968638482872346216645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166624851310496461622193 1624968638482872346216645)
              ·
                refine ⟨304681619715538564915621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1624968638482872346216645 304681619715538564915621)
                ·
                  refine ⟨57127803696663480921679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304681619715538564915621 57127803696663480921679)
                  ·
                    rfl

theorem cell21_250326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_250326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250326 prefixEnd_250326 := by exact prefixLift 250326
  have htrace : WordTrace (prefixWord ++ tailWord_250326) baseStart_250326 baseEnd_250326 := by
    simpa [prefixWord, tailWord_250326, baseEnd_250326] using wordTrace_append hprefix tailTrace_250326
  have hstable : (prefixWord ++ tailWord_250326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250326).length < 2 ^ (prefixWord ++ tailWord_250326).sum := by decide
  have hdescent : baseEnd_250326 < baseStart_250326 := by decide
  rcases family_descends (prefixWord ++ tailWord_250326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250444 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_250444 : Nat := 118140960795 + 250444 * 2 ^ 59
def prefixEnd_250444 : Nat := 4983230072969 + 3 ^ 40 * 250444 * 2
def baseEnd_250444 : Nat := 57154732904321497954771

theorem tailTrace_250444 : CollatzResearch.WordTrace tailWord_250444 prefixEnd_250444 57154732904321497954771 := by
  unfold tailWord_250444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567221552345817637511193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6089628736461090183348257 4567221552345817637511193)
  ·
    refine ⟨3425416164259363228133395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4567221552345817637511193 3425416164259363228133395)
    ·
      refine ⟨5138124246389044842200093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425416164259363228133395 5138124246389044842200093)
      ·
        refine ⟨1926796592395891815825035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5138124246389044842200093 1926796592395891815825035)
        ·
          refine ⟨2890194888593837723737553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926796592395891815825035 2890194888593837723737553)
          ·
            refine ⟨2167646166445378292803165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2890194888593837723737553 2167646166445378292803165)
            ·
              refine ⟨812867312417016859801187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2167646166445378292803165 812867312417016859801187)
              ·
                refine ⟨1219300968625525289701781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812867312417016859801187 1219300968625525289701781)
                ·
                  refine ⟨57154732904321497954771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1219300968625525289701781 57154732904321497954771)
                  ·
                    rfl

theorem cell21_250444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_250444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250444 prefixEnd_250444 := by exact prefixLift 250444
  have htrace : WordTrace (prefixWord ++ tailWord_250444) baseStart_250444 baseEnd_250444 := by
    simpa [prefixWord, tailWord_250444, baseEnd_250444] using wordTrace_append hprefix tailTrace_250444
  have hstable : (prefixWord ++ tailWord_250444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250444).length < 2 ^ (prefixWord ++ tailWord_250444).sum := by decide
  have hdescent : baseEnd_250444 < baseStart_250444 := by decide
  rcases family_descends (prefixWord ++ tailWord_250444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250498 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_250498 : Nat := 118140960795 + 250498 * 2 ^ 59
def prefixEnd_250498 : Nat := 4983230072969 + 3 ^ 40 * 250498 * 2
def baseEnd_250498 : Nat := 57167056440029404054661

theorem tailTrace_250498 : CollatzResearch.WordTrace tailWord_250498 prefixEnd_250498 57167056440029404054661 := by
  unfold tailWord_250498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284103161624000624372037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6090941764330668331658765 2284103161624000624372037)
  ·
    refine ⟨428269342804500117069757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2284103161624000624372037 428269342804500117069757)
    ·
      refine ⟨160601003551687543901159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428269342804500117069757 160601003551687543901159)
      ·
        refine ⟨240901505327531315851739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160601003551687543901159 240901505327531315851739)
        ·
          refine ⟨361352257991296973777609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240901505327531315851739 361352257991296973777609)
          ·
            refine ⟨271014193493472730333207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361352257991296973777609 271014193493472730333207)
            ·
              refine ⟨406521290240209095499811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271014193493472730333207 406521290240209095499811)
              ·
                refine ⟨609781935360313643249717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406521290240209095499811 609781935360313643249717)
                ·
                  refine ⟨57167056440029404054661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609781935360313643249717 57167056440029404054661)
                  ·
                    rfl

theorem cell21_250498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_250498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250498 prefixEnd_250498 := by exact prefixLift 250498
  have htrace : WordTrace (prefixWord ++ tailWord_250498) baseStart_250498 baseEnd_250498 := by
    simpa [prefixWord, tailWord_250498, baseEnd_250498] using wordTrace_append hprefix tailTrace_250498
  have hstable : (prefixWord ++ tailWord_250498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250498).length < 2 ^ (prefixWord ++ tailWord_250498).sum := by decide
  have hdescent : baseEnd_250498 < baseStart_250498 := by decide
  rcases family_descends (prefixWord ++ tailWord_250498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250551 : List Nat := [1, 1, 3, 1, 7, 8]
def baseStart_250551 : Nat := 118140960795 + 250551 * 2 ^ 59
def prefixEnd_250551 : Nat := 4983230072969 + 3 ^ 40 * 250551 * 2
def baseEnd_250551 : Nat := 2117746361559744061897

theorem tailTrace_250551 : CollatzResearch.WordTrace tailWord_250551 prefixEnd_250551 2117746361559744061897 := by
  unfold tailWord_250551
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138345715303992549167507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6092230476869328366111671 9138345715303992549167507)
  ·
    refine ⟨13707518572955988823751261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138345715303992549167507 13707518572955988823751261)
    ·
      refine ⟨5140319464858495808906723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13707518572955988823751261 5140319464858495808906723)
      ·
        refine ⟨7710479197287743713360085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140319464858495808906723 7710479197287743713360085)
        ·
          refine ⟨180714356186431493281877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7710479197287743713360085 180714356186431493281877)
          ·
            refine ⟨2117746361559744061897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 180714356186431493281877 2117746361559744061897)
            ·
              rfl

theorem cell21_250551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 8].length) (baseStart_250551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250551 prefixEnd_250551 := by exact prefixLift 250551
  have htrace : WordTrace (prefixWord ++ tailWord_250551) baseStart_250551 baseEnd_250551 := by
    simpa [prefixWord, tailWord_250551, baseEnd_250551] using wordTrace_append hprefix tailTrace_250551
  have hstable : (prefixWord ++ tailWord_250551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250551).length < 2 ^ (prefixWord ++ tailWord_250551).sum := by decide
  have hdescent : baseEnd_250551 < baseStart_250551 := by decide
  rcases family_descends (prefixWord ++ tailWord_250551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250641 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_250641 : Nat := 118140960795 + 250641 * 2 ^ 59
def prefixEnd_250641 : Nat := 4983230072969 + 3 ^ 40 * 250641 * 2
def baseEnd_250641 : Nat := 57199690988292933171035

theorem tailTrace_250641 : CollatzResearch.WordTrace tailWord_250641 prefixEnd_250641 57199690988292933171035 := by
  unfold tailWord_250641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141628284977937919943777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6094418856651958613295851 9141628284977937919943777)
  ·
    refine ⟨6856221213733453439957833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9141628284977937919943777 6856221213733453439957833)
    ·
      refine ⟨5142165910300090079968375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6856221213733453439957833 5142165910300090079968375)
      ·
        refine ⟨7713248865450135119952563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142165910300090079968375 7713248865450135119952563)
        ·
          refine ⟨11569873298175202679928845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7713248865450135119952563 11569873298175202679928845)
          ·
            refine ⟨4338702486815701004973317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11569873298175202679928845 4338702486815701004973317)
            ·
              refine ⟨813506716277943938432497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4338702486815701004973317 813506716277943938432497)
              ·
                refine ⟨610130037208457953824373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813506716277943938432497 610130037208457953824373)
                ·
                  refine ⟨57199690988292933171035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610130037208457953824373 57199690988292933171035)
                  ·
                    rfl

theorem cell21_250641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_250641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250641 prefixEnd_250641 := by exact prefixLift 250641
  have htrace : WordTrace (prefixWord ++ tailWord_250641) baseStart_250641 baseEnd_250641 := by
    simpa [prefixWord, tailWord_250641, baseEnd_250641] using wordTrace_append hprefix tailTrace_250641
  have hstable : (prefixWord ++ tailWord_250641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250641).length < 2 ^ (prefixWord ++ tailWord_250641).sum := by decide
  have hdescent : baseEnd_250641 < baseStart_250641 := by decide
  rcases family_descends (prefixWord ++ tailWord_250641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250731 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_250731 : Nat := 118140960795 + 250731 * 2 ^ 59
def prefixEnd_250731 : Nat := 4983230072969 + 3 ^ 40 * 250731 * 2
def baseEnd_250731 : Nat := 57220230214472776670851

theorem tailTrace_250731 : CollatzResearch.WordTrace tailWord_250731 prefixEnd_250731 57220230214472776670851 := by
  unfold tailWord_250731
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144910854651883290720047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6096607236434588860480031 9144910854651883290720047)
  ·
    refine ⟨13717366281977824936080071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144910854651883290720047 13717366281977824936080071)
    ·
      refine ⟨20576049422966737404120107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13717366281977824936080071 20576049422966737404120107)
      ·
        refine ⟨30864074134450106106180161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20576049422966737404120107 30864074134450106106180161)
        ·
          refine ⟨23148055600837579579635121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30864074134450106106180161 23148055600837579579635121)
          ·
            refine ⟨17361041700628184684726341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23148055600837579579635121 17361041700628184684726341)
            ·
              refine ⟨3255195318867784628386189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17361041700628184684726341 3255195318867784628386189)
              ·
                refine ⟨1220698244575419235644821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3255195318867784628386189 1220698244575419235644821)
                ·
                  refine ⟨57220230214472776670851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1220698244575419235644821 57220230214472776670851)
                  ·
                    rfl

theorem cell21_250731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_250731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250731 prefixEnd_250731 := by exact prefixLift 250731
  have htrace : WordTrace (prefixWord ++ tailWord_250731) baseStart_250731 baseEnd_250731 := by
    simpa [prefixWord, tailWord_250731, baseEnd_250731] using wordTrace_append hprefix tailTrace_250731
  have hstable : (prefixWord ++ tailWord_250731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250731).length < 2 ^ (prefixWord ++ tailWord_250731).sum := by decide
  have hdescent : baseEnd_250731 < baseStart_250731 := by decide
  rcases family_descends (prefixWord ++ tailWord_250731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250754 : List Nat := [3, 4, 2, 2, 1, 1, 3, 5]
def baseStart_250754 : Nat := 118140960795 + 250754 * 2 ^ 59
def prefixEnd_250754 : Nat := 4983230072969 + 3 ^ 40 * 250754 * 2
def baseEnd_250754 : Nat := 19075159709276615929157

theorem tailTrace_250754 : CollatzResearch.WordTrace tailWord_250754 prefixEnd_250754 19075159709276615929157 := by
  unfold tailWord_250754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286437433392139554701829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6097166489045705479204877 2286437433392139554701829)
  ·
    refine ⟨428707018761026166506593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2286437433392139554701829 428707018761026166506593)
    ·
      refine ⟨321530264070769624879945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428707018761026166506593 321530264070769624879945)
      ·
        refine ⟨241147698053077218659959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321530264070769624879945 241147698053077218659959)
        ·
          refine ⟨361721547079615827989939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241147698053077218659959 361721547079615827989939)
          ·
            refine ⟨542582320619423741984909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361721547079615827989939 542582320619423741984909)
            ·
              refine ⟨203468370232283903244341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542582320619423741984909 203468370232283903244341)
              ·
                refine ⟨19075159709276615929157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203468370232283903244341 19075159709276615929157)
                ·
                  rfl

theorem cell21_250754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_250754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250754 prefixEnd_250754 := by exact prefixLift 250754
  have htrace : WordTrace (prefixWord ++ tailWord_250754) baseStart_250754 baseEnd_250754 := by
    simpa [prefixWord, tailWord_250754, baseEnd_250754] using wordTrace_append hprefix tailTrace_250754
  have hstable : (prefixWord ++ tailWord_250754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250754).length < 2 ^ (prefixWord ++ tailWord_250754).sum := by decide
  have hdescent : baseEnd_250754 < baseStart_250754 := by decide
  rcases family_descends (prefixWord ++ tailWord_250754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250793 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_250793 : Nat := 118140960795 + 250793 * 2 ^ 59
def prefixEnd_250793 : Nat := 4983230072969 + 3 ^ 40 * 250793 * 2
def baseEnd_250793 : Nat := 57234379459174446637391

theorem tailTrace_250793 : CollatzResearch.WordTrace tailWord_250793 prefixEnd_250793 57234379459174446637391 := by
  unfold tailWord_250793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147172180427267879477033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6098114786951511919651355 9147172180427267879477033)
  ·
    refine ⟨6860379135320450909607775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9147172180427267879477033 6860379135320450909607775)
    ·
      refine ⟨10290568702980676364411663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860379135320450909607775 10290568702980676364411663)
      ·
        refine ⟨15435853054471014546617495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10290568702980676364411663 15435853054471014546617495)
        ·
          refine ⟨23153779581706521819926243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435853054471014546617495 23153779581706521819926243)
          ·
            refine ⟨34730669372559782729889365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23153779581706521819926243 34730669372559782729889365)
            ·
              refine ⟨407000031709684953865891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 34730669372559782729889365 407000031709684953865891)
              ·
                refine ⟨610500047564527430798837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407000031709684953865891 610500047564527430798837)
                ·
                  refine ⟨57234379459174446637391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610500047564527430798837 57234379459174446637391)
                  ·
                    rfl

theorem cell21_250793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_250793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250793 prefixEnd_250793 := by exact prefixLift 250793
  have htrace : WordTrace (prefixWord ++ tailWord_250793) baseStart_250793 baseEnd_250793 := by
    simpa [prefixWord, tailWord_250793, baseEnd_250793] using wordTrace_append hprefix tailTrace_250793
  have hstable : (prefixWord ++ tailWord_250793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250793).length < 2 ^ (prefixWord ++ tailWord_250793).sum := by decide
  have hdescent : baseEnd_250793 < baseStart_250793 := by decide
  rcases family_descends (prefixWord ++ tailWord_250793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250813 : List Nat := [1, 4, 1, 2, 5, 1, 2, 5]
def baseStart_250813 : Nat := 118140960795 + 250813 * 2 ^ 59
def prefixEnd_250813 : Nat := 4983230072969 + 3 ^ 40 * 250813 * 2
def baseEnd_250813 : Nat := 19079647910552952101339

theorem tailTrace_250813 : CollatzResearch.WordTrace tailWord_250813 prefixEnd_250813 19079647910552952101339 := by
  unfold tailWord_250813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147901640354811295205093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6098601093569874196803395 9147901640354811295205093)
  ·
    refine ⟨1715231557566527117850955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9147901640354811295205093 1715231557566527117850955)
    ·
      refine ⟨2572847336349790676776433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715231557566527117850955 2572847336349790676776433)
      ·
        refine ⟨1929635502262343007582325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2572847336349790676776433 1929635502262343007582325)
        ·
          refine ⟨180903328337094656960843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1929635502262343007582325 180903328337094656960843)
          ·
            refine ⟨271354992505641985441265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180903328337094656960843 271354992505641985441265)
            ·
              refine ⟨203516244379231489080949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271354992505641985441265 203516244379231489080949)
              ·
                refine ⟨19079647910552952101339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203516244379231489080949 19079647910552952101339)
                ·
                  rfl

theorem cell21_250813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 5].length) (baseStart_250813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250813 prefixEnd_250813 := by exact prefixLift 250813
  have htrace : WordTrace (prefixWord ++ tailWord_250813) baseStart_250813 baseEnd_250813 := by
    simpa [prefixWord, tailWord_250813, baseEnd_250813] using wordTrace_append hprefix tailTrace_250813
  have hstable : (prefixWord ++ tailWord_250813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250813).length < 2 ^ (prefixWord ++ tailWord_250813).sum := by decide
  have hdescent : baseEnd_250813 < baseStart_250813 := by decide
  rcases family_descends (prefixWord ++ tailWord_250813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250827 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 3]
def baseStart_250827 : Nat := 118140960795 + 250827 * 2 ^ 59
def prefixEnd_250827 : Nat := 4983230072969 + 3 ^ 40 * 250827 * 2
def baseEnd_250827 : Nat := 57242138722397943070655

theorem tailTrace_250827 : CollatzResearch.WordTrace tailWord_250827 prefixEnd_250827 57242138722397943070655 := by
  unfold tailWord_250827
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148412262304091686214735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6098941508202727790809823 9148412262304091686214735)
  ·
    refine ⟨13722618393456137529322103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9148412262304091686214735 13722618393456137529322103)
    ·
      refine ⟨20583927590184206293983155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722618393456137529322103 20583927590184206293983155)
      ·
        refine ⟨30875891385276309440974733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20583927590184206293983155 30875891385276309440974733)
        ·
          refine ⟨11578459269478616040365525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30875891385276309440974733 11578459269478616040365525)
          ·
            refine ⟨271370139128405063446067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11578459269478616040365525 271370139128405063446067)
            ·
              refine ⟨407055208692607595169101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271370139128405063446067 407055208692607595169101)
              ·
                refine ⟨152645703259727848188413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407055208692607595169101 152645703259727848188413)
                ·
                  refine ⟨57242138722397943070655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152645703259727848188413 57242138722397943070655)
                  ·
                    rfl

theorem cell21_250827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3].length) (baseStart_250827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250827 prefixEnd_250827 := by exact prefixLift 250827
  have htrace : WordTrace (prefixWord ++ tailWord_250827) baseStart_250827 baseEnd_250827 := by
    simpa [prefixWord, tailWord_250827, baseEnd_250827] using wordTrace_append hprefix tailTrace_250827
  have hstable : (prefixWord ++ tailWord_250827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250827).length < 2 ^ (prefixWord ++ tailWord_250827).sum := by decide
  have hdescent : baseEnd_250827 < baseStart_250827 := by decide
  rcases family_descends (prefixWord ++ tailWord_250827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250855 : List Nat := [1, 1, 5, 2, 2, 2, 2, 6]
def baseStart_250855 : Nat := 118140960795 + 250855 * 2 ^ 59
def prefixEnd_250855 : Nat := 4983230072969 + 3 ^ 40 * 250855 * 2
def baseEnd_250855 : Nat := 19082842901292038867977

theorem tailTrace_250855 : CollatzResearch.WordTrace tailWord_250855 prefixEnd_250855 19082842901292038867977 := by
  unfold tailWord_250855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149433506202652468234019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6099622337468434978822679 9149433506202652468234019)
  ·
    refine ⟨13724150259303978702351029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149433506202652468234019 13724150259303978702351029)
    ·
      refine ⟨1286639086809748003345409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13724150259303978702351029 1286639086809748003345409)
      ·
        refine ⟨964979315107311002509057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286639086809748003345409 964979315107311002509057)
        ·
          refine ⟨723734486330483251881793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964979315107311002509057 723734486330483251881793)
          ·
            refine ⟨542800864747862438911345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723734486330483251881793 542800864747862438911345)
            ·
              refine ⟨407100648560896829183509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542800864747862438911345 407100648560896829183509)
              ·
                refine ⟨19082842901292038867977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 407100648560896829183509 19082842901292038867977)
                ·
                  rfl

theorem cell21_250855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_250855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250855 prefixEnd_250855 := by exact prefixLift 250855
  have htrace : WordTrace (prefixWord ++ tailWord_250855) baseStart_250855 baseEnd_250855 := by
    simpa [prefixWord, tailWord_250855, baseEnd_250855] using wordTrace_append hprefix tailTrace_250855
  have hstable : (prefixWord ++ tailWord_250855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250855).length < 2 ^ (prefixWord ++ tailWord_250855).sum := by decide
  have hdescent : baseEnd_250855 < baseStart_250855 := by decide
  rcases family_descends (prefixWord ++ tailWord_250855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250858 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_250858 : Nat := 118140960795 + 250858 * 2 ^ 59
def prefixEnd_250858 : Nat := 4983230072969 + 3 ^ 40 * 250858 * 2
def baseEnd_250858 : Nat := 57249213344748778053925

theorem tailTrace_250858 : CollatzResearch.WordTrace tailWord_250858 prefixEnd_250858 57249213344748778053925 := by
  unfold tailWord_250858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287385731297945995148307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6099695283461189320395485 2287385731297945995148307)
  ·
    refine ⟨3431078596946918992722461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287385731297945995148307 3431078596946918992722461)
    ·
      refine ⟨1286654473855094622270923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3431078596946918992722461 1286654473855094622270923)
      ·
        refine ⟨1929981710782641933406385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286654473855094622270923 1929981710782641933406385)
        ·
          refine ⟨1447486283086981450054789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929981710782641933406385 1447486283086981450054789)
          ·
            refine ⟨271403678078809021885273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1447486283086981450054789 271403678078809021885273)
            ·
              refine ⟨203552758559106766413955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271403678078809021885273 203552758559106766413955)
              ·
                refine ⟨305329137838660149620933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203552758559106766413955 305329137838660149620933)
                ·
                  refine ⟨57249213344748778053925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305329137838660149620933 57249213344748778053925)
                  ·
                    rfl

theorem cell21_250858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_250858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250858 prefixEnd_250858 := by exact prefixLift 250858
  have htrace : WordTrace (prefixWord ++ tailWord_250858) baseStart_250858 baseEnd_250858 := by
    simpa [prefixWord, tailWord_250858, baseEnd_250858] using wordTrace_append hprefix tailTrace_250858
  have hstable : (prefixWord ++ tailWord_250858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250858).length < 2 ^ (prefixWord ++ tailWord_250858).sum := by decide
  have hdescent : baseEnd_250858 < baseStart_250858 := by decide
  rcases family_descends (prefixWord ++ tailWord_250858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250903 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 3]
def baseStart_250903 : Nat := 118140960795 + 250903 * 2 ^ 59
def prefixEnd_250903 : Nat := 4983230072969 + 3 ^ 40 * 250903 * 2
def baseEnd_250903 : Nat := 57259482957838699803833

theorem tailTrace_250903 : CollatzResearch.WordTrace tailWord_250903 prefixEnd_250903 57259482957838699803833 := by
  unfold tailWord_250903
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151184210028756665981363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6100789473352504443987575 9151184210028756665981363)
  ·
    refine ⟨13726776315043134998972045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9151184210028756665981363 13726776315043134998972045)
    ·
      refine ⟨5147541118141175624614517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13726776315043134998972045 5147541118141175624614517)
      ·
        refine ⟨482581979825735214807611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5147541118141175624614517 482581979825735214807611)
        ·
          refine ⟨723872969738602822211417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482581979825735214807611 723872969738602822211417)
          ·
            refine ⟨542904727303952116658563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723872969738602822211417 542904727303952116658563)
            ·
              refine ⟨814357090955928174987845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542904727303952116658563 814357090955928174987845)
              ·
                refine ⟨152691954554236532810221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814357090955928174987845 152691954554236532810221)
                ·
                  refine ⟨57259482957838699803833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152691954554236532810221 57259482957838699803833)
                  ·
                    rfl

theorem cell21_250903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 3].length) (baseStart_250903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250903 prefixEnd_250903 := by exact prefixLift 250903
  have htrace : WordTrace (prefixWord ++ tailWord_250903) baseStart_250903 baseEnd_250903 := by
    simpa [prefixWord, tailWord_250903, baseEnd_250903] using wordTrace_append hprefix tailTrace_250903
  have hstable : (prefixWord ++ tailWord_250903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250903).length < 2 ^ (prefixWord ++ tailWord_250903).sum := by decide
  have hdescent : baseEnd_250903 < baseStart_250903 := by decide
  rcases family_descends (prefixWord ++ tailWord_250903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250962 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_250962 : Nat := 118140960795 + 250962 * 2 ^ 59
def prefixEnd_250962 : Nat := 4983230072969 + 3 ^ 40 * 250962 * 2
def baseEnd_250962 : Nat := 57272947561667708320379

theorem tailTrace_250962 : CollatzResearch.WordTrace tailWord_250962 prefixEnd_250962 57272947561667708320379 := by
  unfold tailWord_250962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288334029203752435594785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6102224077876673161586093 2288334029203752435594785)
  ·
    refine ⟨1716250521902814326696089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2288334029203752435594785 1716250521902814326696089)
    ·
      refine ⟨1287187891427110745022067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1716250521902814326696089 1287187891427110745022067)
      ·
        refine ⟨1930781837140666117533101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287187891427110745022067 1930781837140666117533101)
        ·
          refine ⟨724043188927749794074913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1930781837140666117533101 724043188927749794074913)
          ·
            refine ⟨543032391695812345556185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724043188927749794074913 543032391695812345556185)
            ·
              refine ⟨407274293771859259167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543032391695812345556185 407274293771859259167139)
              ·
                refine ⟨610911440657788888750709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407274293771859259167139 610911440657788888750709)
                ·
                  refine ⟨57272947561667708320379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610911440657788888750709 57272947561667708320379)
                  ·
                    rfl

theorem cell21_250962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_250962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_250962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_250962 prefixEnd_250962 := by exact prefixLift 250962
  have htrace : WordTrace (prefixWord ++ tailWord_250962) baseStart_250962 baseEnd_250962 := by
    simpa [prefixWord, tailWord_250962, baseEnd_250962] using wordTrace_append hprefix tailTrace_250962
  have hstable : (prefixWord ++ tailWord_250962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250962).length < 2 ^ (prefixWord ++ tailWord_250962).sum := by decide
  have hdescent : baseEnd_250962 < baseStart_250962 := by decide
  rcases family_descends (prefixWord ++ tailWord_250962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251072 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_251072 : Nat := 118140960795 + 251072 * 2 ^ 59
def prefixEnd_251072 : Nat := 4983230072969 + 3 ^ 40 * 251072 * 2
def baseEnd_251072 : Nat := 57298051060331961486821

theorem tailTrace_251072 : CollatzResearch.WordTrace tailWord_251072 prefixEnd_251072 57298051060331961486821 := by
  unfold tailWord_251072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578674073208249264441735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6104898764277665685922313 4578674073208249264441735)
  ·
    refine ⟨6868011109812373896662603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578674073208249264441735 6868011109812373896662603)
    ·
      refine ⟨10302016664718560844993905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6868011109812373896662603 10302016664718560844993905)
      ·
        refine ⟨7726512498538920633745429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10302016664718560844993905 7726512498538920633745429)
        ·
          refine ⟨362180273369011904706817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7726512498538920633745429 362180273369011904706817)
          ·
            refine ⟨271635205026758928530113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362180273369011904706817 271635205026758928530113)
            ·
              refine ⟨203726403770069196397585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271635205026758928530113 203726403770069196397585)
              ·
                refine ⟨152794802827551897298189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203726403770069196397585 152794802827551897298189)
                ·
                  refine ⟨57298051060331961486821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152794802827551897298189 57298051060331961486821)
                  ·
                    rfl

theorem cell21_251072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_251072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251072 prefixEnd_251072 := by exact prefixLift 251072
  have htrace : WordTrace (prefixWord ++ tailWord_251072) baseStart_251072 baseEnd_251072 := by
    simpa [prefixWord, tailWord_251072, baseEnd_251072] using wordTrace_append hprefix tailTrace_251072
  have hstable : (prefixWord ++ tailWord_251072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251072).length < 2 ^ (prefixWord ++ tailWord_251072).sum := by decide
  have hdescent : baseEnd_251072 < baseStart_251072 := by decide
  rcases family_descends (prefixWord ++ tailWord_251072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251114 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_251114 : Nat := 118140960795 + 251114 * 2 ^ 59
def prefixEnd_251114 : Nat := 4983230072969 + 3 ^ 40 * 251114 * 2
def baseEnd_251114 : Nat := 57307636032549221786735

theorem tailTrace_251114 : CollatzResearch.WordTrace tailWord_251114 prefixEnd_251114 57307636032549221786735 := by
  unfold tailWord_251114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289720003066084925478099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6105920008176226467941597 2289720003066084925478099)
  ·
    refine ⟨3434580004599127388217149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289720003066084925478099 3434580004599127388217149)
    ·
      refine ⟨1287967501724672770581431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3434580004599127388217149 1287967501724672770581431)
      ·
        refine ⟨1931951252587009155872147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287967501724672770581431 1931951252587009155872147)
        ·
          refine ⟨2897926878880513733808221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931951252587009155872147 2897926878880513733808221)
          ·
            refine ⟨1086722579580192650178083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2897926878880513733808221 1086722579580192650178083)
            ·
              refine ⟨1630083869370288975267125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086722579580192650178083 1630083869370288975267125)
              ·
                refine ⟨152820362753464591431293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1630083869370288975267125 152820362753464591431293)
                ·
                  refine ⟨57307636032549221786735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152820362753464591431293 57307636032549221786735)
                  ·
                    rfl

theorem cell21_251114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_251114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251114 prefixEnd_251114 := by exact prefixLift 251114
  have htrace : WordTrace (prefixWord ++ tailWord_251114) baseStart_251114 baseEnd_251114 := by
    simpa [prefixWord, tailWord_251114, baseEnd_251114] using wordTrace_append hprefix tailTrace_251114
  have hstable : (prefixWord ++ tailWord_251114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251114).length < 2 ^ (prefixWord ++ tailWord_251114).sum := by decide
  have hdescent : baseEnd_251114 < baseStart_251114 := by decide
  rcases family_descends (prefixWord ++ tailWord_251114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251187 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_251187 : Nat := 118140960795 + 251187 * 2 ^ 59
def prefixEnd_251187 : Nat := 4983230072969 + 3 ^ 40 * 251187 * 2
def baseEnd_251187 : Nat := 57324295627117317069919

theorem tailTrace_251187 : CollatzResearch.WordTrace tailWord_251187 prefixEnd_251187 57324295627117317069919 := by
  unfold tailWord_251187
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161542540999873169319815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6107695027333248779546543 9161542540999873169319815)
  ·
    refine ⟨13742313811499809753979723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9161542540999873169319815 13742313811499809753979723)
    ·
      refine ⟨20613470717249714630969585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13742313811499809753979723 20613470717249714630969585)
      ·
        refine ⟨15460103037937285973227189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20613470717249714630969585 15460103037937285973227189)
        ·
          refine ⟨1449384659806620559990049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15460103037937285973227189 1449384659806620559990049)
          ·
            refine ⟨1087038494854965419992537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449384659806620559990049 1087038494854965419992537)
            ·
              refine ⟨815278871141224064994403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087038494854965419992537 815278871141224064994403)
              ·
                refine ⟨1222918306711836097491605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815278871141224064994403 1222918306711836097491605)
                ·
                  refine ⟨57324295627117317069919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1222918306711836097491605 57324295627117317069919)
                  ·
                    rfl

theorem cell21_251187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_251187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251187 prefixEnd_251187 := by exact prefixLift 251187
  have htrace : WordTrace (prefixWord ++ tailWord_251187) baseStart_251187 baseEnd_251187 := by
    simpa [prefixWord, tailWord_251187, baseEnd_251187] using wordTrace_append hprefix tailTrace_251187
  have hstable : (prefixWord ++ tailWord_251187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251187).length < 2 ^ (prefixWord ++ tailWord_251187).sum := by decide
  have hdescent : baseEnd_251187 < baseStart_251187 := by decide
  rcases family_descends (prefixWord ++ tailWord_251187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251266 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_251266 : Nat := 118140960795 + 251266 * 2 ^ 59
def prefixEnd_251266 : Nat := 4983230072969 + 3 ^ 40 * 251266 * 2
def baseEnd_251266 : Nat := 57342324503430735253091

theorem tailTrace_251266 : CollatzResearch.WordTrace tailWord_251266 prefixEnd_251266 57342324503430735253091 := by
  unfold tailWord_251266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291105976928417415361413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6109615938475779774297101 2291105976928417415361413)
  ·
    refine ⟨429582370674078265380265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2291105976928417415361413 429582370674078265380265)
    ·
      refine ⟨322186778005558699035199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429582370674078265380265 322186778005558699035199)
      ·
        refine ⟨483280167008338048552799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322186778005558699035199 483280167008338048552799)
        ·
          refine ⟨724920250512507072829199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483280167008338048552799 724920250512507072829199)
          ·
            refine ⟨1087380375768760609243799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724920250512507072829199 1087380375768760609243799)
            ·
              refine ⟨1631070563653140913865699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087380375768760609243799 1631070563653140913865699)
              ·
                refine ⟨2446605845479711370798549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631070563653140913865699 2446605845479711370798549)
                ·
                  refine ⟨57342324503430735253091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2446605845479711370798549 57342324503430735253091)
                  ·
                    rfl

theorem cell21_251266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_251266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251266 prefixEnd_251266 := by exact prefixLift 251266
  have htrace : WordTrace (prefixWord ++ tailWord_251266) baseStart_251266 baseEnd_251266 := by
    simpa [prefixWord, tailWord_251266, baseEnd_251266] using wordTrace_append hprefix tailTrace_251266
  have hstable : (prefixWord ++ tailWord_251266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251266).length < 2 ^ (prefixWord ++ tailWord_251266).sum := by decide
  have hdescent : baseEnd_251266 < baseStart_251266 := by decide
  rcases family_descends (prefixWord ++ tailWord_251266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251308 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_251308 : Nat := 118140960795 + 251308 * 2 ^ 59
def prefixEnd_251308 : Nat := 4983230072969 + 3 ^ 40 * 251308 * 2
def baseEnd_251308 : Nat := 57351909475647995553005

theorem tailTrace_251308 : CollatzResearch.WordTrace tailWord_251308 prefixEnd_251308 57351909475647995553005 := by
  unfold tailWord_251308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582977886780755417237289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6110637182374340556316385 4582977886780755417237289)
  ·
    refine ⟨3437233415085566562927967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4582977886780755417237289 3437233415085566562927967)
    ·
      refine ⟨5155850122628349844391951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437233415085566562927967 5155850122628349844391951)
      ·
        refine ⟨7733775183942524766587927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5155850122628349844391951 7733775183942524766587927)
        ·
          refine ⟨11600662775913787149881891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733775183942524766587927 11600662775913787149881891)
          ·
            refine ⟨17400994163870680724822837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600662775913787149881891 17400994163870680724822837)
            ·
              refine ⟨1631343202862876317952141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17400994163870680724822837 1631343202862876317952141)
              ·
                refine ⟨611753701073578619232053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631343202862876317952141 611753701073578619232053)
                ·
                  refine ⟨57351909475647995553005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 611753701073578619232053 57351909475647995553005)
                  ·
                    rfl

theorem cell21_251308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_251308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251308 prefixEnd_251308 := by exact prefixLift 251308
  have htrace : WordTrace (prefixWord ++ tailWord_251308) baseStart_251308 baseEnd_251308 := by
    simpa [prefixWord, tailWord_251308, baseEnd_251308] using wordTrace_append hprefix tailTrace_251308
  have hstable : (prefixWord ++ tailWord_251308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251308).length < 2 ^ (prefixWord ++ tailWord_251308).sum := by decide
  have hdescent : baseEnd_251308 < baseStart_251308 := by decide
  rcases family_descends (prefixWord ++ tailWord_251308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251342 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_251342 : Nat := 118140960795 + 251342 * 2 ^ 59
def prefixEnd_251342 : Nat := 4983230072969 + 3 ^ 40 * 251342 * 2
def baseEnd_251342 : Nat := 57359668738871491986269

theorem tailTrace_251342 : CollatzResearch.WordTrace tailWord_251342 prefixEnd_251342 57359668738871491986269 := by
  unfold tailWord_251342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145899481929791830151535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6111463903625556427474853 1145899481929791830151535)
  ·
    refine ⟨1718849222894687745227303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145899481929791830151535 1718849222894687745227303)
    ·
      refine ⟨2578273834342031617840955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718849222894687745227303 2578273834342031617840955)
      ·
        refine ⟨3867410751513047426761433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578273834342031617840955 3867410751513047426761433)
        ·
          refine ⟨2900558063634785570071075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3867410751513047426761433 2900558063634785570071075)
          ·
            refine ⟨4350837095452178355106613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900558063634785570071075 4350837095452178355106613)
            ·
              refine ⟨407890977698641720791245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4350837095452178355106613 407890977698641720791245)
              ·
                refine ⟨152959116636990645296717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407890977698641720791245 152959116636990645296717)
                ·
                  refine ⟨57359668738871491986269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152959116636990645296717 57359668738871491986269)
                  ·
                    rfl

theorem cell21_251342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_251342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251342 prefixEnd_251342 := by exact prefixLift 251342
  have htrace : WordTrace (prefixWord ++ tailWord_251342) baseStart_251342 baseEnd_251342 := by
    simpa [prefixWord, tailWord_251342, baseEnd_251342] using wordTrace_append hprefix tailTrace_251342
  have hstable : (prefixWord ++ tailWord_251342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251342).length < 2 ^ (prefixWord ++ tailWord_251342).sum := by decide
  have hdescent : baseEnd_251342 < baseStart_251342 := by decide
  rcases family_descends (prefixWord ++ tailWord_251342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251353 : List Nat := [1, 2, 1, 2, 4, 2, 9]
def baseStart_251353 : Nat := 118140960795 + 251353 * 2 ^ 59
def prefixEnd_251353 : Nat := 4983230072969 + 3 ^ 40 * 251353 * 2
def baseEnd_251353 : Nat := 6373575454304213033657

theorem tailTrace_251353 : CollatzResearch.WordTrace tailWord_251353 prefixEnd_251353 6373575454304213033657 := by
  unfold tailWord_251353
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167597058398483519862713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6111731372265655679908475 9167597058398483519862713)
  ·
    refine ⟨6875697793798862639897035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9167597058398483519862713 6875697793798862639897035)
    ·
      refine ⟨10313546690698293959845553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6875697793798862639897035 10313546690698293959845553)
      ·
        refine ⟨7735160018023720469884165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10313546690698293959845553 7735160018023720469884165)
        ·
          refine ⟨1450342503379447588103281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7735160018023720469884165 1450342503379447588103281)
          ·
            refine ⟨1087756877534585691077461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450342503379447588103281 1087756877534585691077461)
            ·
              refine ⟨6373575454304213033657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1087756877534585691077461 6373575454304213033657)
              ·
                rfl

theorem cell21_251353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 9].length) (baseStart_251353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251353 prefixEnd_251353 := by exact prefixLift 251353
  have htrace : WordTrace (prefixWord ++ tailWord_251353) baseStart_251353 baseEnd_251353 := by
    simpa [prefixWord, tailWord_251353, baseEnd_251353] using wordTrace_append hprefix tailTrace_251353
  have hstable : (prefixWord ++ tailWord_251353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251353).length < 2 ^ (prefixWord ++ tailWord_251353).sum := by decide
  have hdescent : baseEnd_251353 < baseStart_251353 := by decide
  rcases family_descends (prefixWord ++ tailWord_251353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251373 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_251373 : Nat := 118140960795 + 251373 * 2 ^ 59
def prefixEnd_251373 : Nat := 4983230072969 + 3 ^ 40 * 251373 * 2
def baseEnd_251373 : Nat := 57366743361222326969539

theorem tailTrace_251373 : CollatzResearch.WordTrace tailWord_251373 prefixEnd_251373 57366743361222326969539 := by
  unfold tailWord_251373
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168326518326026935590773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6112217678884017957060515 9168326518326026935590773)
  ·
    refine ⟨859530611093065025211635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9168326518326026935590773 859530611093065025211635)
    ·
      refine ⟨1289295916639597537817453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859530611093065025211635 1289295916639597537817453)
      ·
        refine ⟨483485968739849076681545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1289295916639597537817453 483485968739849076681545)
        ·
          refine ⟨362614476554886807511159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483485968739849076681545 362614476554886807511159)
          ·
            refine ⟨543921714832330211266739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362614476554886807511159 543921714832330211266739)
            ·
              refine ⟨815882572248495316900109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543921714832330211266739 815882572248495316900109)
              ·
                refine ⟨305955964593185743837541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815882572248495316900109 305955964593185743837541)
                ·
                  refine ⟨57366743361222326969539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305955964593185743837541 57366743361222326969539)
                  ·
                    rfl

theorem cell21_251373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_251373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251373 prefixEnd_251373 := by exact prefixLift 251373
  have htrace : WordTrace (prefixWord ++ tailWord_251373) baseStart_251373 baseEnd_251373 := by
    simpa [prefixWord, tailWord_251373, baseEnd_251373] using wordTrace_append hprefix tailTrace_251373
  have hstable : (prefixWord ++ tailWord_251373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251373).length < 2 ^ (prefixWord ++ tailWord_251373).sum := by decide
  have hdescent : baseEnd_251373 < baseStart_251373 := by decide
  rcases family_descends (prefixWord ++ tailWord_251373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251401 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 3]
def baseStart_251401 : Nat := 118140960795 + 251401 * 2 ^ 59
def prefixEnd_251401 : Nat := 4983230072969 + 3 ^ 40 * 251401 * 2
def baseEnd_251401 : Nat := 57373133342700500502815

theorem tailTrace_251401 : CollatzResearch.WordTrace tailWord_251401 prefixEnd_251401 57373133342700500502815 := by
  unfold tailWord_251401
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169347762224587717610057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6112898508149725145073371 9169347762224587717610057)
  ·
    refine ⟨6877010821668440788207543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9169347762224587717610057 6877010821668440788207543)
    ·
      refine ⟨10315516232502661182311315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877010821668440788207543 10315516232502661182311315)
      ·
        refine ⟨15473274348753991773466973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10315516232502661182311315 15473274348753991773466973)
        ·
          refine ⟨5802477880782746915050115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15473274348753991773466973 5802477880782746915050115)
          ·
            refine ⟨8703716821174120372575173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802477880782746915050115 8703716821174120372575173)
            ·
              refine ⟨1631946903970147569857845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8703716821174120372575173 1631946903970147569857845)
              ·
                refine ⟨152995022247201334674173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1631946903970147569857845 152995022247201334674173)
                ·
                  refine ⟨57373133342700500502815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152995022247201334674173 57373133342700500502815)
                  ·
                    rfl

theorem cell21_251401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_251401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251401 prefixEnd_251401 := by exact prefixLift 251401
  have htrace : WordTrace (prefixWord ++ tailWord_251401) baseStart_251401 baseEnd_251401 := by
    simpa [prefixWord, tailWord_251401, baseEnd_251401] using wordTrace_append hprefix tailTrace_251401
  have hstable : (prefixWord ++ tailWord_251401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251401).length < 2 ^ (prefixWord ++ tailWord_251401).sum := by decide
  have hdescent : baseEnd_251401 < baseStart_251401 := by decide
  rcases family_descends (prefixWord ++ tailWord_251401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251528 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_251528 : Nat := 118140960795 + 251528 * 2 ^ 59
def prefixEnd_251528 : Nat := 4983230072969 + 3 ^ 40 * 251528 * 2
def baseEnd_251528 : Nat := 57402116472976501885889

theorem tailTrace_251528 : CollatzResearch.WordTrace tailWord_251528 prefixEnd_251528 57402116472976501885889 := by
  unfold tailWord_251528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586989916382244203741619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6115986555176325604988825 4586989916382244203741619)
  ·
    refine ⟨6880484874573366305612429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586989916382244203741619 6880484874573366305612429)
    ·
      refine ⟨2580181827965012364604661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6880484874573366305612429 2580181827965012364604661)
      ·
        refine ⟨241892046371719909181687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2580181827965012364604661 241892046371719909181687)
        ·
          refine ⟨362838069557579863772531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241892046371719909181687 362838069557579863772531)
          ·
            refine ⟨544257104336369795658797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362838069557579863772531 544257104336369795658797)
            ·
              refine ⟨204096414126138673372049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544257104336369795658797 204096414126138673372049)
              ·
                refine ⟨153072310594604005029037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204096414126138673372049 153072310594604005029037)
                ·
                  refine ⟨57402116472976501885889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153072310594604005029037 57402116472976501885889)
                  ·
                    rfl

theorem cell21_251528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_251528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251528 prefixEnd_251528 := by exact prefixLift 251528
  have htrace : WordTrace (prefixWord ++ tailWord_251528) baseStart_251528 baseEnd_251528 := by
    simpa [prefixWord, tailWord_251528, baseEnd_251528] using wordTrace_append hprefix tailTrace_251528
  have hstable : (prefixWord ++ tailWord_251528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251528).length < 2 ^ (prefixWord ++ tailWord_251528).sum := by decide
  have hdescent : baseEnd_251528 < baseStart_251528 := by decide
  rcases family_descends (prefixWord ++ tailWord_251528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251595 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_251595 : Nat := 118140960795 + 251595 * 2 ^ 59
def prefixEnd_251595 : Nat := 4983230072969 + 3 ^ 40 * 251595 * 2
def baseEnd_251595 : Nat := 57417406785799274269085

theorem tailTrace_251595 : CollatzResearch.WordTrace tailWord_251595 prefixEnd_251595 57417406785799274269085 := by
  unfold tailWord_251595
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176423523521758850172239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6117615682347839233448159 9176423523521758850172239)
  ·
    refine ⟨13764635285282638275258359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176423523521758850172239 13764635285282638275258359)
    ·
      refine ⟨20646952927923957412887539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13764635285282638275258359 20646952927923957412887539)
      ·
        refine ⟨30970429391885936119331309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20646952927923957412887539 30970429391885936119331309)
        ·
          refine ⟨11613911021957226044749241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30970429391885936119331309 11613911021957226044749241)
          ·
            refine ⟨8710433266467919533561931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613911021957226044749241 8710433266467919533561931)
            ·
              refine ⟨13065649899701879300342897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710433266467919533561931 13065649899701879300342897)
              ·
                refine ⟨9799237424776409475257173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13065649899701879300342897 9799237424776409475257173)
                ·
                  refine ⟨57417406785799274269085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9799237424776409475257173 57417406785799274269085)
                  ·
                    rfl

theorem cell21_251595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_251595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251595 prefixEnd_251595 := by exact prefixLift 251595
  have htrace : WordTrace (prefixWord ++ tailWord_251595) baseStart_251595 baseEnd_251595 := by
    simpa [prefixWord, tailWord_251595, baseEnd_251595] using wordTrace_append hprefix tailTrace_251595
  have hstable : (prefixWord ++ tailWord_251595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251595).length < 2 ^ (prefixWord ++ tailWord_251595).sum := by decide
  have hdescent : baseEnd_251595 < baseStart_251595 := by decide
  rcases family_descends (prefixWord ++ tailWord_251595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251646 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_251646 : Nat := 118140960795 + 251646 * 2 ^ 59
def prefixEnd_251646 : Nat := 4983230072969 + 3 ^ 40 * 251646 * 2
def baseEnd_251646 : Nat := 57429045680634518918981

theorem tailTrace_251646 : CollatzResearch.WordTrace tailWord_251646 prefixEnd_251646 57429045680634518918981 := by
  unfold tailWord_251646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147285455792124320034849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6118855764224663040185861 1147285455792124320034849)
  ·
    refine ⟨860464091844093240026137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1147285455792124320034849 860464091844093240026137)
    ·
      refine ⟨645348068883069930019603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 860464091844093240026137 645348068883069930019603)
      ·
        refine ⟨968022103324604895029405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645348068883069930019603 968022103324604895029405)
        ·
          refine ⟨363008288746726835636027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968022103324604895029405 363008288746726835636027)
          ·
            refine ⟨544512433120090253454041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363008288746726835636027 544512433120090253454041)
            ·
              refine ⟨408384324840067690090531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544512433120090253454041 408384324840067690090531)
              ·
                refine ⟨612576487260101535135797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408384324840067690090531 612576487260101535135797)
                ·
                  refine ⟨57429045680634518918981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 612576487260101535135797 57429045680634518918981)
                  ·
                    rfl

theorem cell21_251646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_251646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251646 prefixEnd_251646 := by exact prefixLift 251646
  have htrace : WordTrace (prefixWord ++ tailWord_251646) baseStart_251646 baseEnd_251646 := by
    simpa [prefixWord, tailWord_251646, baseEnd_251646] using wordTrace_append hprefix tailTrace_251646
  have hstable : (prefixWord ++ tailWord_251646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251646).length < 2 ^ (prefixWord ++ tailWord_251646).sum := by decide
  have hdescent : baseEnd_251646 < baseStart_251646 := by decide
  rcases family_descends (prefixWord ++ tailWord_251646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251674 : List Nat := [3, 1, 1, 3, 2, 2, 4, 5]
def baseStart_251674 : Nat := 118140960795 + 251674 * 2 ^ 59
def prefixEnd_251674 : Nat := 4983230072969 + 3 ^ 40 * 251674 * 2
def baseEnd_251674 : Nat := 19145145220704230817419

theorem tailTrace_251674 : CollatzResearch.WordTrace tailWord_251674 prefixEnd_251674 19145145220704230817419 := by
  unfold tailWord_251674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294826222558888835574519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6119536593490370228198717 2294826222558888835574519)
  ·
    refine ⟨3442239333838333253361779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294826222558888835574519 3442239333838333253361779)
    ·
      refine ⟨5163359000757499880042669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442239333838333253361779 5163359000757499880042669)
      ·
        refine ⟨1936259625284062455016001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5163359000757499880042669 1936259625284062455016001)
        ·
          refine ⟨1452194718963046841262001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936259625284062455016001 1452194718963046841262001)
          ·
            refine ⟨1089146039222285130946501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452194718963046841262001 1089146039222285130946501)
            ·
              refine ⟨204214882354178462052469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1089146039222285130946501 204214882354178462052469)
              ·
                refine ⟨19145145220704230817419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204214882354178462052469 19145145220704230817419)
                ·
                  rfl

theorem cell21_251674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_251674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251674 prefixEnd_251674 := by exact prefixLift 251674
  have htrace : WordTrace (prefixWord ++ tailWord_251674) baseStart_251674 baseEnd_251674 := by
    simpa [prefixWord, tailWord_251674, baseEnd_251674] using wordTrace_append hprefix tailTrace_251674
  have hstable : (prefixWord ++ tailWord_251674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251674).length < 2 ^ (prefixWord ++ tailWord_251674).sum := by decide
  have hdescent : baseEnd_251674 < baseStart_251674 := by decide
  rcases family_descends (prefixWord ++ tailWord_251674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251733 : List Nat := [1, 3, 2, 2, 2, 2, 2, 7]
def baseStart_251733 : Nat := 118140960795 + 251733 * 2 ^ 59
def prefixEnd_251733 : Nat := 4983230072969 + 3 ^ 40 * 251733 * 2
def baseEnd_251733 : Nat := 19149633421980566989601

theorem tailTrace_251733 : CollatzResearch.WordTrace tailWord_251733 prefixEnd_251733 19149633421980566989601 := by
  unfold tailWord_251733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181456797021808418695853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6120971198014538945797235 9181456797021808418695853)
  ·
    refine ⟨3443046298883178157010945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9181456797021808418695853 3443046298883178157010945)
    ·
      refine ⟨2582284724162383617758209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443046298883178157010945 2582284724162383617758209)
      ·
        refine ⟨1936713543121787713318657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2582284724162383617758209 1936713543121787713318657)
        ·
          refine ⟨1452535157341340784988993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936713543121787713318657 1452535157341340784988993)
          ·
            refine ⟨1089401368006005588741745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452535157341340784988993 1089401368006005588741745)
            ·
              refine ⟨817051026004504191556309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089401368006005588741745 817051026004504191556309)
              ·
                refine ⟨19149633421980566989601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 817051026004504191556309 19149633421980566989601)
                ·
                  rfl

theorem cell21_251733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_251733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251733 prefixEnd_251733 := by exact prefixLift 251733
  have htrace : WordTrace (prefixWord ++ tailWord_251733) baseStart_251733 baseEnd_251733 := by
    simpa [prefixWord, tailWord_251733, baseEnd_251733] using wordTrace_append hprefix tailTrace_251733
  have hstable : (prefixWord ++ tailWord_251733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251733).length < 2 ^ (prefixWord ++ tailWord_251733).sum := by decide
  have hdescent : baseEnd_251733 < baseStart_251733 := by decide
  rcases family_descends (prefixWord ++ tailWord_251733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251812 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_251812 : Nat := 118140960795 + 251812 * 2 ^ 59
def prefixEnd_251812 : Nat := 4983230072969 + 3 ^ 40 * 251812 * 2
def baseEnd_251812 : Nat := 57466929142255119151975

theorem tailTrace_251812 : CollatzResearch.WordTrace tailWord_251812 prefixEnd_251812 57466929142255119151975 := by
  unfold tailWord_251812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592169081867802455410845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6122892109157069940547793 4592169081867802455410845)
  ·
    refine ⟨1722063405700425920779067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4592169081867802455410845 1722063405700425920779067)
    ·
      refine ⟨2583095108550638881168601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722063405700425920779067 2583095108550638881168601)
      ·
        refine ⟨1937321331412979160876451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2583095108550638881168601 1937321331412979160876451)
        ·
          refine ⟨2905981997119468741314677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937321331412979160876451 2905981997119468741314677)
          ·
            refine ⟨272435812229950194498251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2905981997119468741314677 272435812229950194498251)
            ·
              refine ⟨408653718344925291747377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272435812229950194498251 408653718344925291747377)
              ·
                refine ⟨306490288758693968810533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408653718344925291747377 306490288758693968810533)
                ·
                  refine ⟨57466929142255119151975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306490288758693968810533 57466929142255119151975)
                  ·
                    rfl

theorem cell21_251812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_251812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251812 prefixEnd_251812 := by exact prefixLift 251812
  have htrace : WordTrace (prefixWord ++ tailWord_251812) baseStart_251812 baseEnd_251812 := by
    simpa [prefixWord, tailWord_251812, baseEnd_251812] using wordTrace_append hprefix tailTrace_251812
  have hstable : (prefixWord ++ tailWord_251812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251812).length < 2 ^ (prefixWord ++ tailWord_251812).sum := by decide
  have hdescent : baseEnd_251812 < baseStart_251812 := by decide
  rcases family_descends (prefixWord ++ tailWord_251812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251854 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_251854 : Nat := 118140960795 + 251854 * 2 ^ 59
def prefixEnd_251854 : Nat := 4983230072969 + 3 ^ 40 * 251854 * 2
def baseEnd_251854 : Nat := 57476514114472379451889

theorem tailTrace_251854 : CollatzResearch.WordTrace tailWord_251854 prefixEnd_251854 57476514114472379451889 := by
  unfold tailWord_251854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148233753697930760481327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6123913353055630722567077 1148233753697930760481327)
  ·
    refine ⟨1722350630546896140721991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1148233753697930760481327 1722350630546896140721991)
    ·
      refine ⟨2583525945820344211082987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722350630546896140721991 2583525945820344211082987)
      ·
        refine ⟨3875288918730516316624481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583525945820344211082987 3875288918730516316624481)
        ·
          refine ⟨2906466689047887237468361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3875288918730516316624481 2906466689047887237468361)
          ·
            refine ⟨2179850016785915428101271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906466689047887237468361 2179850016785915428101271)
            ·
              refine ⟨3269775025178873142151907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179850016785915428101271 3269775025178873142151907)
              ·
                refine ⟨4904662537768309713227861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269775025178873142151907 4904662537768309713227861)
                ·
                  refine ⟨57476514114472379451889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4904662537768309713227861 57476514114472379451889)
                  ·
                    rfl

theorem cell21_251854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_251854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251854 prefixEnd_251854 := by exact prefixLift 251854
  have htrace : WordTrace (prefixWord ++ tailWord_251854) baseStart_251854 baseEnd_251854 := by
    simpa [prefixWord, tailWord_251854, baseEnd_251854] using wordTrace_append hprefix tailTrace_251854
  have hstable : (prefixWord ++ tailWord_251854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251854).length < 2 ^ (prefixWord ++ tailWord_251854).sum := by decide
  have hdescent : baseEnd_251854 < baseStart_251854 := by decide
  rcases family_descends (prefixWord ++ tailWord_251854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251899 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_251899 : Nat := 118140960795 + 251899 * 2 ^ 59
def prefixEnd_251899 : Nat := 4983230072969 + 3 ^ 40 * 251899 * 2
def baseEnd_251899 : Nat := 57486783727562301201797

theorem tailTrace_251899 : CollatzResearch.WordTrace tailWord_251899 prefixEnd_251899 57486783727562301201797 := by
  unfold tailWord_251899
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187511314420418769238751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6125007542946945846159167 9187511314420418769238751)
  ·
    refine ⟨13781266971630628153858127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187511314420418769238751 13781266971630628153858127)
    ·
      refine ⟨20671900457445942230787191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13781266971630628153858127 20671900457445942230787191)
      ·
        refine ⟨31007850686168913346180787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671900457445942230787191 31007850686168913346180787)
        ·
          refine ⟨46511776029253370019271181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31007850686168913346180787 46511776029253370019271181)
          ·
            refine ⟨17441916010970013757226693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46511776029253370019271181 17441916010970013757226693)
            ·
              refine ⟨3270359252056877579480005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17441916010970013757226693 3270359252056877579480005)
              ·
                refine ⟨613192359760664546152501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3270359252056877579480005 613192359760664546152501)
                ·
                  refine ⟨57486783727562301201797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613192359760664546152501 57486783727562301201797)
                  ·
                    rfl

theorem cell21_251899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_251899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251899 prefixEnd_251899 := by exact prefixLift 251899
  have htrace : WordTrace (prefixWord ++ tailWord_251899) baseStart_251899 baseEnd_251899 := by
    simpa [prefixWord, tailWord_251899, baseEnd_251899] using wordTrace_append hprefix tailTrace_251899
  have hstable : (prefixWord ++ tailWord_251899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251899).length < 2 ^ (prefixWord ++ tailWord_251899).sum := by decide
  have hdescent : baseEnd_251899 < baseStart_251899 := by decide
  rcases family_descends (prefixWord ++ tailWord_251899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251902 : List Nat := [4, 2, 2, 2, 1, 1, 2, 7]
def baseStart_251902 : Nat := 118140960795 + 251902 * 2 ^ 59
def prefixEnd_251902 : Nat := 4983230072969 + 3 ^ 40 * 251902 * 2
def baseEnd_251902 : Nat := 19162489456144987550597

theorem tailTrace_251902 : CollatzResearch.WordTrace tailWord_251902 prefixEnd_251902 19162489456144987550597 := by
  unfold tailWord_251902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148452591676193785199745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6125080488939700187731973 1148452591676193785199745)
  ·
    refine ⟨861339443757145338899809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1148452591676193785199745 861339443757145338899809)
    ·
      refine ⟨646004582817859004174857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861339443757145338899809 646004582817859004174857)
      ·
        refine ⟨484503437113394253131143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646004582817859004174857 484503437113394253131143)
        ·
          refine ⟨726755155670091379696715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484503437113394253131143 726755155670091379696715)
          ·
            refine ⟨1090132733505137069545073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726755155670091379696715 1090132733505137069545073)
            ·
              refine ⟨817599550128852802158805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090132733505137069545073 817599550128852802158805)
              ·
                refine ⟨19162489456144987550597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 817599550128852802158805 19162489456144987550597)
                ·
                  rfl

theorem cell21_251902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_251902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251902 prefixEnd_251902 := by exact prefixLift 251902
  have htrace : WordTrace (prefixWord ++ tailWord_251902) baseStart_251902 baseEnd_251902 := by
    simpa [prefixWord, tailWord_251902, baseEnd_251902] using wordTrace_append hprefix tailTrace_251902
  have hstable : (prefixWord ++ tailWord_251902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251902).length < 2 ^ (prefixWord ++ tailWord_251902).sum := by decide
  have hdescent : baseEnd_251902 < baseStart_251902 := by decide
  rcases family_descends (prefixWord ++ tailWord_251902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251975 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_251975 : Nat := 118140960795 + 251975 * 2 ^ 59
def prefixEnd_251975 : Nat := 4983230072969 + 3 ^ 40 * 251975 * 2
def baseEnd_251975 : Nat := 57504127963003057934975

theorem tailTrace_251975 : CollatzResearch.WordTrace tailWord_251975 prefixEnd_251975 57504127963003057934975 := by
  unfold tailWord_251975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9190283262145083749005379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6126855508096722499336919 9190283262145083749005379)
  ·
    refine ⟨13785424893217625623508069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9190283262145083749005379 13785424893217625623508069)
    ·
      refine ⟨2584767167478304804407763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13785424893217625623508069 2584767167478304804407763)
      ·
        refine ⟨3877150751217457206611645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584767167478304804407763 3877150751217457206611645)
        ·
          refine ⟨1453931531706546452479367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3877150751217457206611645 1453931531706546452479367)
          ·
            refine ⟨2180897297559819678719051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453931531706546452479367 2180897297559819678719051)
            ·
              refine ⟨3271345946339729518078577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180897297559819678719051 3271345946339729518078577)
              ·
                refine ⟨2453509459754797138558933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271345946339729518078577 2453509459754797138558933)
                ·
                  refine ⟨57504127963003057934975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2453509459754797138558933 57504127963003057934975)
                  ·
                    rfl

theorem cell21_251975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_251975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251975 prefixEnd_251975 := by exact prefixLift 251975
  have htrace : WordTrace (prefixWord ++ tailWord_251975) baseStart_251975 baseEnd_251975 := by
    simpa [prefixWord, tailWord_251975, baseEnd_251975] using wordTrace_append hprefix tailTrace_251975
  have hstable : (prefixWord ++ tailWord_251975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251975).length < 2 ^ (prefixWord ++ tailWord_251975).sum := by decide
  have hdescent : baseEnd_251975 < baseStart_251975 := by decide
  rcases family_descends (prefixWord ++ tailWord_251975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251992 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_251992 : Nat := 118140960795 + 251992 * 2 ^ 59
def prefixEnd_251992 : Nat := 4983230072969 + 3 ^ 40 * 251992 * 2
def baseEnd_251992 : Nat := 57508007594614806151607

theorem tailTrace_251992 : CollatzResearch.WordTrace tailWord_251992 prefixEnd_251992 57508007594614806151607 := by
  unfold tailWord_251992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595451651541747826187115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6127268868722330434916153 4595451651541747826187115)
  ·
    refine ⟨6893177477312621739280673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4595451651541747826187115 6893177477312621739280673)
    ·
      refine ⟨5169883107984466304460505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6893177477312621739280673 5169883107984466304460505)
      ·
        refine ⟨3877412330988349728345379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5169883107984466304460505 3877412330988349728345379)
        ·
          refine ⟨5816118496482524592518069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877412330988349728345379 5816118496482524592518069)
          ·
            refine ⟨545261109045236680548569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5816118496482524592518069 545261109045236680548569)
            ·
              refine ⟨408945831783927510411427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545261109045236680548569 408945831783927510411427)
              ·
                refine ⟨613418747675891265617141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408945831783927510411427 613418747675891265617141)
                ·
                  refine ⟨57508007594614806151607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613418747675891265617141 57508007594614806151607)
                  ·
                    rfl

theorem cell21_251992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_251992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_251992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_251992 prefixEnd_251992 := by exact prefixLift 251992
  have htrace : WordTrace (prefixWord ++ tailWord_251992) baseStart_251992 baseEnd_251992 := by
    simpa [prefixWord, tailWord_251992, baseEnd_251992] using wordTrace_append hprefix tailTrace_251992
  have hstable : (prefixWord ++ tailWord_251992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251992).length < 2 ^ (prefixWord ++ tailWord_251992).sum := by decide
  have hdescent : baseEnd_251992 < baseStart_251992 := by decide
  rcases family_descends (prefixWord ++ tailWord_251992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252037 : List Nat := [1, 3, 1, 1, 5, 3, 7]
def baseStart_252037 : Nat := 118140960795 + 252037 * 2 ^ 59
def prefixEnd_252037 : Nat := 4983230072969 + 3 ^ 40 * 252037 * 2
def baseEnd_252037 : Nat := 6390919689744969766835

theorem tailTrace_252037 : CollatzResearch.WordTrace tailWord_252037 prefixEnd_252037 6390919689744969766835 := by
  unfold tailWord_252037
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192544587920468337762365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6128363058613645558508243 9192544587920468337762365)
  ·
    refine ⟨3447204220470175626660887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9192544587920468337762365 3447204220470175626660887)
    ·
      refine ⟨5170806330705263439991331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447204220470175626660887 5170806330705263439991331)
      ·
        refine ⟨7756209496057895159986997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170806330705263439991331 7756209496057895159986997)
        ·
          refine ⟨727144640255427671248781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7756209496057895159986997 727144640255427671248781)
          ·
            refine ⟨272679240095785376718293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727144640255427671248781 272679240095785376718293)
            ·
              refine ⟨6390919689744969766835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 272679240095785376718293 6390919689744969766835)
              ·
                rfl

theorem cell21_252037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 7].length) (baseStart_252037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252037 prefixEnd_252037 := by exact prefixLift 252037
  have htrace : WordTrace (prefixWord ++ tailWord_252037) baseStart_252037 baseEnd_252037 := by
    simpa [prefixWord, tailWord_252037, baseEnd_252037] using wordTrace_append hprefix tailTrace_252037
  have hstable : (prefixWord ++ tailWord_252037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252037).length < 2 ^ (prefixWord ++ tailWord_252037).sum := by decide
  have hdescent : baseEnd_252037 < baseStart_252037 := by decide
  rcases family_descends (prefixWord ++ tailWord_252037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252096 : List Nat := [2, 1, 1, 2, 5, 10]
def baseStart_252096 : Nat := 118140960795 + 252096 * 2 ^ 59
def prefixEnd_252096 : Nat := 4983230072969 + 3 ^ 40 * 252096 * 2
def baseEnd_252096 : Nat := 2130805252279027274743

theorem tailTrace_252096 : CollatzResearch.WordTrace tailWord_252096 prefixEnd_252096 2130805252279027274743 := by
  unfold tailWord_252096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597348247353360707080071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6129797663137814276106761 4597348247353360707080071)
  ·
    refine ⟨6896022371030041060620107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597348247353360707080071 6896022371030041060620107)
    ·
      refine ⟨10344033556545061590930161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896022371030041060620107 10344033556545061590930161)
      ·
        refine ⟨7758025167408796193197621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10344033556545061590930161 7758025167408796193197621)
        ·
          refine ⟨727314859444574643112277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7758025167408796193197621 727314859444574643112277)
          ·
            refine ⟨2130805252279027274743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 727314859444574643112277 2130805252279027274743)
            ·
              rfl

theorem cell21_252096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 10].length) (baseStart_252096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252096 prefixEnd_252096 := by exact prefixLift 252096
  have htrace : WordTrace (prefixWord ++ tailWord_252096) baseStart_252096 baseEnd_252096 := by
    simpa [prefixWord, tailWord_252096, baseEnd_252096] using wordTrace_append hprefix tailTrace_252096
  have hstable : (prefixWord ++ tailWord_252096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252096).length < 2 ^ (prefixWord ++ tailWord_252096).sum := by decide
  have hdescent : baseEnd_252096 < baseStart_252096 := by decide
  rcases family_descends (prefixWord ++ tailWord_252096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252172 : List Nat := [2, 2, 1, 2, 2, 2, 2, 8]
def baseStart_252172 : Nat := 118140960795 + 252172 * 2 ^ 59
def prefixEnd_252172 : Nat := 4983230072969 + 3 ^ 40 * 252172 * 2
def baseEnd_252172 : Nat := 19183028682324831050413

theorem tailTrace_252172 : CollatzResearch.WordTrace tailWord_252172 prefixEnd_252172 19183028682324831050413 := by
  unfold tailWord_252172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598734221215693196963385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6131645628287590929284513 4598734221215693196963385)
  ·
    refine ⟨3449050665911769897722539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4598734221215693196963385 3449050665911769897722539)
    ·
      refine ⟨5173575998867654846583809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449050665911769897722539 5173575998867654846583809)
      ·
        refine ⟨3880181999150741134937857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5173575998867654846583809 3880181999150741134937857)
        ·
          refine ⟨2910136499363055851203393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3880181999150741134937857 2910136499363055851203393)
          ·
            refine ⟨2182602374522291888402545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910136499363055851203393 2182602374522291888402545)
            ·
              refine ⟨1636951780891718916301909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182602374522291888402545 1636951780891718916301909)
              ·
                refine ⟨19183028682324831050413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1636951780891718916301909 19183028682324831050413)
                ·
                  rfl

theorem cell21_252172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_252172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252172 prefixEnd_252172 := by exact prefixLift 252172
  have htrace : WordTrace (prefixWord ++ tailWord_252172) baseStart_252172 baseEnd_252172 := by
    simpa [prefixWord, tailWord_252172, baseEnd_252172] using wordTrace_append hprefix tailTrace_252172
  have hstable : (prefixWord ++ tailWord_252172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252172).length < 2 ^ (prefixWord ++ tailWord_252172).sum := by decide
  have hdescent : baseEnd_252172 < baseStart_252172 := by decide
  rcases family_descends (prefixWord ++ tailWord_252172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252293 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_252293 : Nat := 118140960795 + 252293 * 2 ^ 59
def prefixEnd_252293 : Nat := 4983230072969 + 3 ^ 40 * 252293 * 2
def baseEnd_252293 : Nat := 57576699895505171634325

theorem tailTrace_252293 : CollatzResearch.WordTrace tailWord_252293 prefixEnd_252293 57576699895505171634325 := by
  unfold tailWord_252293
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201881674993024059081533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6134587783328682706054355 9201881674993024059081533)
  ·
    refine ⟨3450705628122384022155575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9201881674993024059081533 3450705628122384022155575)
    ·
      refine ⟨5176058442183576033233363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450705628122384022155575 5176058442183576033233363)
      ·
        refine ⟨7764087663275364049850045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5176058442183576033233363 7764087663275364049850045)
        ·
          refine ⟨2911532873728261518693767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7764087663275364049850045 2911532873728261518693767)
          ·
            refine ⟨4367299310592392278040651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911532873728261518693767 4367299310592392278040651)
            ·
              refine ⟨6550948965888588417060977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367299310592392278040651 6550948965888588417060977)
              ·
                refine ⟨4913211724416441312795733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550948965888588417060977 4913211724416441312795733)
                ·
                  refine ⟨57576699895505171634325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4913211724416441312795733 57576699895505171634325)
                  ·
                    rfl

theorem cell21_252293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_252293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252293 prefixEnd_252293 := by exact prefixLift 252293
  have htrace : WordTrace (prefixWord ++ tailWord_252293) baseStart_252293 baseEnd_252293 := by
    simpa [prefixWord, tailWord_252293, baseEnd_252293] using wordTrace_append hprefix tailTrace_252293
  have hstable : (prefixWord ++ tailWord_252293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252293).length < 2 ^ (prefixWord ++ tailWord_252293).sum := by decide
  have hdescent : baseEnd_252293 < baseStart_252293 := by decide
  rcases family_descends (prefixWord ++ tailWord_252293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252327 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_252327 : Nat := 118140960795 + 252327 * 2 ^ 59
def prefixEnd_252327 : Nat := 4983230072969 + 3 ^ 40 * 252327 * 2
def baseEnd_252327 : Nat := 57584459158728668067589

theorem tailTrace_252327 : CollatzResearch.WordTrace tailWord_252327 prefixEnd_252327 57584459158728668067589 := by
  unfold tailWord_252327
  simp only [CollatzResearch.WordTrace]
  refine ⟨9203121756869847865819235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6135414504579898577212823 9203121756869847865819235)
  ·
    refine ⟨13804682635304771798728853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9203121756869847865819235 13804682635304771798728853)
    ·
      refine ⟨647094498529911178065415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13804682635304771798728853 647094498529911178065415)
      ·
        refine ⟨970641747794866767098123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647094498529911178065415 970641747794866767098123)
        ·
          refine ⟨1455962621692300150647185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970641747794866767098123 1455962621692300150647185)
          ·
            refine ⟨1091971966269225112985389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455962621692300150647185 1091971966269225112985389)
            ·
              refine ⟨409489487350959417369521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091971966269225112985389 409489487350959417369521)
              ·
                refine ⟨307117115513219563027141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409489487350959417369521 307117115513219563027141)
                ·
                  refine ⟨57584459158728668067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307117115513219563027141 57584459158728668067589)
                  ·
                    rfl

theorem cell21_252327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_252327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252327 prefixEnd_252327 := by exact prefixLift 252327
  have htrace : WordTrace (prefixWord ++ tailWord_252327) baseStart_252327 baseEnd_252327 := by
    simpa [prefixWord, tailWord_252327, baseEnd_252327] using wordTrace_append hprefix tailTrace_252327
  have hstable : (prefixWord ++ tailWord_252327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252327).length < 2 ^ (prefixWord ++ tailWord_252327).sum := by decide
  have hdescent : baseEnd_252327 < baseStart_252327 := by decide
  rcases family_descends (prefixWord ++ tailWord_252327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252389 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 5]
def baseStart_252389 : Nat := 118140960795 + 252389 * 2 ^ 59
def prefixEnd_252389 : Nat := 4983230072969 + 3 ^ 40 * 252389 * 2
def baseEnd_252389 : Nat := 57598608403430338034129

theorem tailTrace_252389 : CollatzResearch.WordTrace tailWord_252389 prefixEnd_252389 57598608403430338034129 := by
  unfold tailWord_252389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205383082645232454576221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6136922055096821636384147 9205383082645232454576221)
  ·
    refine ⟨3452018655991962170466083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9205383082645232454576221 3452018655991962170466083)
    ·
      refine ⟨5178027983987943255699125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452018655991962170466083 5178027983987943255699125)
      ·
        refine ⟨485440123498869680221793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5178027983987943255699125 485440123498869680221793)
        ·
          refine ⟨364080092624152260166345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485440123498869680221793 364080092624152260166345)
          ·
            refine ⟨273060069468114195124759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364080092624152260166345 273060069468114195124759)
            ·
              refine ⟨409590104202171292687139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273060069468114195124759 409590104202171292687139)
              ·
                refine ⟨614385156303256939030709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409590104202171292687139 614385156303256939030709)
                ·
                  refine ⟨57598608403430338034129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 614385156303256939030709 57598608403430338034129)
                  ·
                    rfl

theorem cell21_252389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_252389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252389 prefixEnd_252389 := by exact prefixLift 252389
  have htrace : WordTrace (prefixWord ++ tailWord_252389) baseStart_252389 baseEnd_252389 := by
    simpa [prefixWord, tailWord_252389, baseEnd_252389] using wordTrace_append hprefix tailTrace_252389
  have hstable : (prefixWord ++ tailWord_252389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252389).length < 2 ^ (prefixWord ++ tailWord_252389).sum := by decide
  have hdescent : baseEnd_252389 < baseStart_252389 := by decide
  rcases family_descends (prefixWord ++ tailWord_252389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252400 : List Nat := [2, 1, 1, 1, 3, 3, 4, 6]
def baseStart_252400 : Nat := 118140960795 + 252400 * 2 ^ 59
def prefixEnd_252400 : Nat := 4983230072969 + 3 ^ 40 * 252400 * 2
def baseEnd_252400 : Nat := 19200372917765587783591

theorem tailTrace_252400 : CollatzResearch.WordTrace tailWord_252400 prefixEnd_252400 19200372917765587783591 := by
  unfold tailWord_252400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602892142802690666613327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6137189523736920888817769 4602892142802690666613327)
  ·
    refine ⟨6904338214204035999919991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602892142802690666613327 6904338214204035999919991)
    ·
      refine ⟨10356507321306053999879987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6904338214204035999919991 10356507321306053999879987)
      ·
        refine ⟨15534760981959080999819981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10356507321306053999879987 15534760981959080999819981)
        ·
          refine ⟨5825535368234655374932493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15534760981959080999819981 5825535368234655374932493)
          ·
            refine ⟨2184575763087995765599685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5825535368234655374932493 2184575763087995765599685)
            ·
              refine ⟨409607955578999206049941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2184575763087995765599685 409607955578999206049941)
              ·
                refine ⟨19200372917765587783591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409607955578999206049941 19200372917765587783591)
                ·
                  rfl

theorem cell21_252400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_252400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252400 prefixEnd_252400 := by exact prefixLift 252400
  have htrace : WordTrace (prefixWord ++ tailWord_252400) baseStart_252400 baseEnd_252400 := by
    simpa [prefixWord, tailWord_252400, baseEnd_252400] using wordTrace_append hprefix tailTrace_252400
  have hstable : (prefixWord ++ tailWord_252400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252400).length < 2 ^ (prefixWord ++ tailWord_252400).sum := by decide
  have hdescent : baseEnd_252400 < baseStart_252400 := by decide
  rcases family_descends (prefixWord ++ tailWord_252400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252493 : List Nat := [1, 6, 1, 1, 2, 2, 8]
def baseStart_252493 : Nat := 118140960795 + 252493 * 2 ^ 59
def prefixEnd_252493 : Nat := 4983230072969 + 3 ^ 40 * 252493 * 2
def baseEnd_252493 : Nat := 6402482513372140922287

theorem tailTrace_252493 : CollatzResearch.WordTrace tailWord_252493 prefixEnd_252493 6402482513372140922287 := by
  unfold tailWord_252493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209176274268458216362133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6139450849512305477574755 9209176274268458216362133)
  ·
    refine ⟨431680137856333978891975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9209176274268458216362133 431680137856333978891975)
    ·
      refine ⟨647520206784500968337963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431680137856333978891975 647520206784500968337963)
      ·
        refine ⟨971280310176751452506945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647520206784500968337963 971280310176751452506945)
        ·
          refine ⟨728460232632563589380209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971280310176751452506945 728460232632563589380209)
          ·
            refine ⟨546345174474422692035157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728460232632563589380209 546345174474422692035157)
            ·
              refine ⟨6402482513372140922287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 546345174474422692035157 6402482513372140922287)
              ·
                rfl

theorem cell21_252493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 8].length) (baseStart_252493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252493 prefixEnd_252493 := by exact prefixLift 252493
  have htrace : WordTrace (prefixWord ++ tailWord_252493) baseStart_252493 baseEnd_252493 := by
    simpa [prefixWord, tailWord_252493, baseEnd_252493] using wordTrace_append hprefix tailTrace_252493
  have hstable : (prefixWord ++ tailWord_252493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252493).length < 2 ^ (prefixWord ++ tailWord_252493).sum := by decide
  have hdescent : baseEnd_252493 < baseStart_252493 := by decide
  rcases family_descends (prefixWord ++ tailWord_252493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252572 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_252572 : Nat := 118140960795 + 252572 * 2 ^ 59
def prefixEnd_252572 : Nat := 4983230072969 + 3 ^ 40 * 252572 * 2
def baseEnd_252572 : Nat := 57640371496662686483755

theorem tailTrace_252572 : CollatzResearch.WordTrace tailWord_252572 prefixEnd_252572 57640371496662686483755 := by
  unfold tailWord_252572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606028820491127354243985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6141371760654836472325313 4606028820491127354243985)
  ·
    refine ⟨3454521615368345515682989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4606028820491127354243985 3454521615368345515682989)
    ·
      refine ⟨1295445605763129568381121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3454521615368345515682989 1295445605763129568381121)
      ·
        refine ⟨971584204322347176285841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295445605763129568381121 971584204322347176285841)
        ·
          refine ⟨728688153241760382214381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971584204322347176285841 728688153241760382214381)
          ·
            refine ⟨273258057465660143330393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 728688153241760382214381 273258057465660143330393)
            ·
              refine ⟨204943543099245107497795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273258057465660143330393 204943543099245107497795)
              ·
                refine ⟨307415314648867661246693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204943543099245107497795 307415314648867661246693)
                ·
                  refine ⟨57640371496662686483755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307415314648867661246693 57640371496662686483755)
                  ·
                    rfl

theorem cell21_252572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_252572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252572 prefixEnd_252572 := by exact prefixLift 252572
  have htrace : WordTrace (prefixWord ++ tailWord_252572) baseStart_252572 baseEnd_252572 := by
    simpa [prefixWord, tailWord_252572, baseEnd_252572] using wordTrace_append hprefix tailTrace_252572
  have hstable : (prefixWord ++ tailWord_252572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252572).length < 2 ^ (prefixWord ++ tailWord_252572).sum := by decide
  have hdescent : baseEnd_252572 < baseStart_252572 := by decide
  rcases family_descends (prefixWord ++ tailWord_252572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252645 : List Nat := [1, 3, 1, 4, 1, 3, 3, 5]
def baseStart_252645 : Nat := 118140960795 + 252645 * 2 ^ 59
def prefixEnd_252645 : Nat := 4983230072969 + 3 ^ 40 * 252645 * 2
def baseEnd_252645 : Nat := 19219010363743593922313

theorem tailTrace_252645 : CollatzResearch.WordTrace tailWord_252645 prefixEnd_252645 19219010363743593922313 := by
  unfold tailWord_252645
  simp only [CollatzResearch.WordTrace]
  refine ⟨9214720169717788175895389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6143146779811858783930259 9214720169717788175895389)
  ·
    refine ⟨3455520063644170565960771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9214720169717788175895389 3455520063644170565960771)
    ·
      refine ⟨5183280095466255848941157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455520063644170565960771 5183280095466255848941157)
      ·
        refine ⟨971865017899922971676467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5183280095466255848941157 971865017899922971676467)
        ·
          refine ⟨1457797526849884457514701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971865017899922971676467 1457797526849884457514701)
          ·
            refine ⟨546674072568706671568013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1457797526849884457514701 546674072568706671568013)
            ·
              refine ⟨205002777213265001838005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546674072568706671568013 205002777213265001838005)
              ·
                refine ⟨19219010363743593922313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205002777213265001838005 19219010363743593922313)
                ·
                  rfl

theorem cell21_252645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 5].length) (baseStart_252645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252645 prefixEnd_252645 := by exact prefixLift 252645
  have htrace : WordTrace (prefixWord ++ tailWord_252645) baseStart_252645 baseEnd_252645 := by
    simpa [prefixWord, tailWord_252645, baseEnd_252645] using wordTrace_append hprefix tailTrace_252645
  have hstable : (prefixWord ++ tailWord_252645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252645).length < 2 ^ (prefixWord ++ tailWord_252645).sum := by decide
  have hdescent : baseEnd_252645 < baseStart_252645 := by decide
  rcases family_descends (prefixWord ++ tailWord_252645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252676 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_252676 : Nat := 118140960795 + 252676 * 2 ^ 59
def prefixEnd_252676 : Nat := 4983230072969 + 3 ^ 40 * 252676 * 2
def baseEnd_252676 : Nat := 57664105713581616750209

theorem tailTrace_252676 : CollatzResearch.WordTrace tailWord_252676 prefixEnd_252676 57664105713581616750209 := by
  unfold tailWord_252676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607925416302740235136941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6143900555070320313515921 4607925416302740235136941)
  ·
    refine ⟨1727972031113527588176353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4607925416302740235136941 1727972031113527588176353)
    ·
      refine ⟨1295979023335145691132265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1727972031113527588176353 1295979023335145691132265)
      ·
        refine ⟨971984267501359268349199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295979023335145691132265 971984267501359268349199)
        ·
          refine ⟨1457976401252038902523799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971984267501359268349199 1457976401252038902523799)
          ·
            refine ⟨2186964601878058353785699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457976401252038902523799 2186964601878058353785699)
            ·
              refine ⟨3280446902817087530678549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186964601878058353785699 3280446902817087530678549)
              ·
                refine ⟨153770948569550978000557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3280446902817087530678549 153770948569550978000557)
                ·
                  refine ⟨57664105713581616750209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153770948569550978000557 57664105713581616750209)
                  ·
                    rfl

theorem cell21_252676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_252676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252676 prefixEnd_252676 := by exact prefixLift 252676
  have htrace : WordTrace (prefixWord ++ tailWord_252676) baseStart_252676 baseEnd_252676 := by
    simpa [prefixWord, tailWord_252676, baseEnd_252676] using wordTrace_append hprefix tailTrace_252676
  have hstable : (prefixWord ++ tailWord_252676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252676).length < 2 ^ (prefixWord ++ tailWord_252676).sum := by decide
  have hdescent : baseEnd_252676 < baseStart_252676 := by decide
  rcases family_descends (prefixWord ++ tailWord_252676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252687 : List Nat := [1, 1, 2, 1, 1, 1, 6, 8]
def baseStart_252687 : Nat := 118140960795 + 252687 * 2 ^ 59
def prefixEnd_252687 : Nat := 4983230072969 + 3 ^ 40 * 252687 * 2
def baseEnd_252687 : Nat := 19222205354482680688951

theorem tailTrace_252687 : CollatzResearch.WordTrace tailWord_252687 prefixEnd_252687 19222205354482680688951 := by
  unfold tailWord_252687
  simp only [CollatzResearch.WordTrace]
  refine ⟨9216252035565629348924315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6144168023710419565949543 9216252035565629348924315)
  ·
    refine ⟨13824378053348444023386473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9216252035565629348924315 13824378053348444023386473)
    ·
      refine ⟨10368283540011333017539855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13824378053348444023386473 10368283540011333017539855)
      ·
        refine ⟨15552425310016999526309783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368283540011333017539855 15552425310016999526309783)
        ·
          refine ⟨23328637965025499289464675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552425310016999526309783 23328637965025499289464675)
          ·
            refine ⟨34992956947538248934197013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23328637965025499289464675 34992956947538248934197013)
            ·
              refine ⟨1640294856915855418790485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34992956947538248934197013 1640294856915855418790485)
              ·
                refine ⟨19222205354482680688951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1640294856915855418790485 19222205354482680688951)
                ·
                  rfl

theorem cell21_252687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_252687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252687 prefixEnd_252687 := by exact prefixLift 252687
  have htrace : WordTrace (prefixWord ++ tailWord_252687) baseStart_252687 baseEnd_252687 := by
    simpa [prefixWord, tailWord_252687, baseEnd_252687] using wordTrace_append hprefix tailTrace_252687
  have hstable : (prefixWord ++ tailWord_252687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252687).length < 2 ^ (prefixWord ++ tailWord_252687).sum := by decide
  have hdescent : baseEnd_252687 < baseStart_252687 := by decide
  rcases family_descends (prefixWord ++ tailWord_252687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252704 : List Nat := [2, 1, 1, 5, 1, 3, 1, 7]
def baseStart_252704 : Nat := 118140960795 + 252704 * 2 ^ 59
def prefixEnd_252704 : Nat := 4983230072969 + 3 ^ 40 * 252704 * 2
def baseEnd_252704 : Nat := 19223498565019930094495

theorem tailTrace_252704 : CollatzResearch.WordTrace tailWord_252704 prefixEnd_252704 19223498565019930094495 := by
  unfold tailWord_252704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608436038252020626146583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6144581384336027501528777 4608436038252020626146583)
  ·
    refine ⟨6912654057378030939219875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608436038252020626146583 6912654057378030939219875)
    ·
      refine ⟨10368981086067046408829813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6912654057378030939219875 10368981086067046408829813)
      ·
        refine ⟨972091976818785600827795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10368981086067046408829813 972091976818785600827795)
        ·
          refine ⟨1458137965228178401241693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972091976818785600827795 1458137965228178401241693)
          ·
            refine ⟨546801736960566900465635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1458137965228178401241693 546801736960566900465635)
            ·
              refine ⟨820202605440850350698453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546801736960566900465635 820202605440850350698453)
              ·
                refine ⟨19223498565019930094495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 820202605440850350698453 19223498565019930094495)
                ·
                  rfl

theorem cell21_252704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_252704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252704 prefixEnd_252704 := by exact prefixLift 252704
  have htrace : WordTrace (prefixWord ++ tailWord_252704) baseStart_252704 baseEnd_252704 := by
    simpa [prefixWord, tailWord_252704, baseEnd_252704] using wordTrace_append hprefix tailTrace_252704
  have hstable : (prefixWord ++ tailWord_252704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252704).length < 2 ^ (prefixWord ++ tailWord_252704).sum := by decide
  have hdescent : baseEnd_252704 < baseStart_252704 := by decide
  rcases family_descends (prefixWord ++ tailWord_252704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252735 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_252735 : Nat := 118140960795 + 252735 * 2 ^ 59
def prefixEnd_252735 : Nat := 4983230072969 + 3 ^ 40 * 252735 * 2
def baseEnd_252735 : Nat := 57677570317410625266755

theorem tailTrace_252735 : CollatzResearch.WordTrace tailWord_252735 prefixEnd_252735 57677570317410625266755 := by
  unfold tailWord_252735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218002739391733546671659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6145335159594489031114439 9218002739391733546671659)
  ·
    refine ⟨13827004109087600320007489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218002739391733546671659 13827004109087600320007489)
    ·
      refine ⟨10370253081815700240005617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827004109087600320007489 10370253081815700240005617)
      ·
        refine ⟨7777689811361775180004213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10370253081815700240005617 7777689811361775180004213)
        ·
          refine ⟨729158419815166423125395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7777689811361775180004213 729158419815166423125395)
          ·
            refine ⟨1093737629722749634688093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729158419815166423125395 1093737629722749634688093)
            ·
              refine ⟨410151611146031113008035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1093737629722749634688093 410151611146031113008035)
              ·
                refine ⟨615227416719046669512053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410151611146031113008035 615227416719046669512053)
                ·
                  refine ⟨57677570317410625266755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615227416719046669512053 57677570317410625266755)
                  ·
                    rfl

theorem cell21_252735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_252735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252735 prefixEnd_252735 := by exact prefixLift 252735
  have htrace : WordTrace (prefixWord ++ tailWord_252735) baseStart_252735 baseEnd_252735 := by
    simpa [prefixWord, tailWord_252735, baseEnd_252735] using wordTrace_append hprefix tailTrace_252735
  have hstable : (prefixWord ++ tailWord_252735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252735).length < 2 ^ (prefixWord ++ tailWord_252735).sum := by decide
  have hdescent : baseEnd_252735 < baseStart_252735 := by decide
  rcases family_descends (prefixWord ++ tailWord_252735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252794 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_252794 : Nat := 118140960795 + 252794 * 2 ^ 59
def prefixEnd_252794 : Nat := 4983230072969 + 3 ^ 40 * 252794 * 2
def baseEnd_252794 : Nat := 57691034921239633783301

theorem tailTrace_252794 : CollatzResearch.WordTrace tailWord_252794 prefixEnd_252794 57691034921239633783301 := by
  unfold tailWord_252794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305038661544496655767359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6146769764118657748712957 2305038661544496655767359)
  ·
    refine ⟨3457557992316744983651039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305038661544496655767359 3457557992316744983651039)
    ·
      refine ⟨5186336988475117475476559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457557992316744983651039 5186336988475117475476559)
      ·
        refine ⟨7779505482712676213214839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5186336988475117475476559 7779505482712676213214839)
        ·
          refine ⟨11669258224069014319822259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7779505482712676213214839 11669258224069014319822259)
          ·
            refine ⟨17503887336103521479733389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11669258224069014319822259 17503887336103521479733389)
            ·
              refine ⟨6563957751038820554900021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17503887336103521479733389 6563957751038820554900021)
              ·
                refine ⟨615371039159889427021877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6563957751038820554900021 615371039159889427021877)
                ·
                  refine ⟨57691034921239633783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615371039159889427021877 57691034921239633783301)
                  ·
                    rfl

theorem cell21_252794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_252794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252794 prefixEnd_252794 := by exact prefixLift 252794
  have htrace : WordTrace (prefixWord ++ tailWord_252794) baseStart_252794 baseEnd_252794 := by
    simpa [prefixWord, tailWord_252794, baseEnd_252794] using wordTrace_append hprefix tailTrace_252794
  have hstable : (prefixWord ++ tailWord_252794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252794).length < 2 ^ (prefixWord ++ tailWord_252794).sum := by decide
  have hdescent : baseEnd_252794 < baseStart_252794 := by decide
  rcases family_descends (prefixWord ++ tailWord_252794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252845 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 5]
def baseStart_252845 : Nat := 118140960795 + 252845 * 2 ^ 59
def prefixEnd_252845 : Nat := 4983230072969 + 3 ^ 40 * 252845 * 2
def baseEnd_252845 : Nat := 57702673816074878433197

theorem tailTrace_252845 : CollatzResearch.WordTrace tailWord_252845 prefixEnd_252845 57702673816074878433197 := by
  unfold tailWord_252845
  simp only [CollatzResearch.WordTrace]
  refine ⟨9222014768993222333175989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6148009845995481555450659 9222014768993222333175989)
  ·
    refine ⟨864563884593114593735249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9222014768993222333175989 864563884593114593735249)
    ·
      refine ⟨648422913444835945301437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864563884593114593735249 648422913444835945301437)
      ·
        refine ⟨243158592541813479488039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648422913444835945301437 243158592541813479488039)
        ·
          refine ⟨364737888812720219232059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243158592541813479488039 364737888812720219232059)
          ·
            refine ⟨547106833219080328848089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364737888812720219232059 547106833219080328848089)
            ·
              refine ⟨410330124914310246636067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547106833219080328848089 410330124914310246636067)
              ·
                refine ⟨615495187371465369954101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410330124914310246636067 615495187371465369954101)
                ·
                  refine ⟨57702673816074878433197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615495187371465369954101 57702673816074878433197)
                  ·
                    rfl

theorem cell21_252845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_252845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252845 prefixEnd_252845 := by exact prefixLift 252845
  have htrace : WordTrace (prefixWord ++ tailWord_252845) baseStart_252845 baseEnd_252845 := by
    simpa [prefixWord, tailWord_252845, baseEnd_252845] using wordTrace_append hprefix tailTrace_252845
  have hstable : (prefixWord ++ tailWord_252845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252845).length < 2 ^ (prefixWord ++ tailWord_252845).sum := by decide
  have hdescent : baseEnd_252845 < baseStart_252845 := by decide
  rcases family_descends (prefixWord ++ tailWord_252845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252887 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 3]
def baseStart_252887 : Nat := 118140960795 + 252887 * 2 ^ 59
def prefixEnd_252887 : Nat := 4983230072969 + 3 ^ 40 * 252887 * 2
def baseEnd_252887 : Nat := 57712258788292138733111

theorem tailTrace_252887 : CollatzResearch.WordTrace tailWord_252887 prefixEnd_252887 57712258788292138733111 := by
  unfold tailWord_252887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223546634841063506204915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6149031089894042337469943 9223546634841063506204915)
  ·
    refine ⟨13835319952261595259307373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9223546634841063506204915 13835319952261595259307373)
    ·
      refine ⟨5188244982098098222240265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13835319952261595259307373 5188244982098098222240265)
      ·
        refine ⟨3891183736573573666680199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5188244982098098222240265 3891183736573573666680199)
        ·
          refine ⟨5836775604860360500020299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891183736573573666680199 5836775604860360500020299)
          ·
            refine ⟨8755163407290540750030449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836775604860360500020299 8755163407290540750030449)
            ·
              refine ⟨6566372555467905562522837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8755163407290540750030449 6566372555467905562522837)
              ·
                refine ⟨153899356768779036621629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6566372555467905562522837 153899356768779036621629)
                ·
                  refine ⟨57712258788292138733111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153899356768779036621629 57712258788292138733111)
                  ·
                    rfl

theorem cell21_252887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3].length) (baseStart_252887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252887 prefixEnd_252887 := by exact prefixLift 252887
  have htrace : WordTrace (prefixWord ++ tailWord_252887) baseStart_252887 baseEnd_252887 := by
    simpa [prefixWord, tailWord_252887, baseEnd_252887] using wordTrace_append hprefix tailTrace_252887
  have hstable : (prefixWord ++ tailWord_252887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252887).length < 2 ^ (prefixWord ++ tailWord_252887).sum := by decide
  have hdescent : baseEnd_252887 < baseStart_252887 := by decide
  rcases family_descends (prefixWord ++ tailWord_252887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252977 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_252977 : Nat := 118140960795 + 252977 * 2 ^ 59
def prefixEnd_252977 : Nat := 4983230072969 + 3 ^ 40 * 252977 * 2
def baseEnd_252977 : Nat := 57732798014471982232927

theorem tailTrace_252977 : CollatzResearch.WordTrace tailWord_252977 prefixEnd_252977 57732798014471982232927 := by
  unfold tailWord_252977
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226829204515008876981185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6151219469676672584654123 9226829204515008876981185)
  ·
    refine ⟨6920121903386256657735889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9226829204515008876981185 6920121903386256657735889)
    ·
      refine ⟨5190091427539692493301917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6920121903386256657735889 5190091427539692493301917)
      ·
        refine ⟨1946284285327384684988219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5190091427539692493301917 1946284285327384684988219)
        ·
          refine ⟨2919426427991077027482329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946284285327384684988219 2919426427991077027482329)
          ·
            refine ⟨2189569820993307770611747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919426427991077027482329 2189569820993307770611747)
            ·
              refine ⟨3284354731489961655917621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189569820993307770611747 3284354731489961655917621)
              ·
                refine ⟨307908256077183905242277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3284354731489961655917621 307908256077183905242277)
                ·
                  refine ⟨57732798014471982232927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307908256077183905242277 57732798014471982232927)
                  ·
                    rfl

theorem cell21_252977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_252977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252977 prefixEnd_252977 := by exact prefixLift 252977
  have htrace : WordTrace (prefixWord ++ tailWord_252977) baseStart_252977 baseEnd_252977 := by
    simpa [prefixWord, tailWord_252977, baseEnd_252977] using wordTrace_append hprefix tailTrace_252977
  have hstable : (prefixWord ++ tailWord_252977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252977).length < 2 ^ (prefixWord ++ tailWord_252977).sum := by decide
  have hdescent : baseEnd_252977 < baseStart_252977 := by decide
  rcases family_descends (prefixWord ++ tailWord_252977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252980 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_252980 : Nat := 118140960795 + 252980 * 2 ^ 59
def prefixEnd_252980 : Nat := 4983230072969 + 3 ^ 40 * 252980 * 2
def baseEnd_252980 : Nat := 57733482655344643682921

theorem tailTrace_252980 : CollatzResearch.WordTrace tailWord_252980 prefixEnd_252980 57733482655344643682921 := by
  unfold tailWord_252980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613469311752070194670197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6151292415669426926226929 4613469311752070194670197)
  ·
    refine ⟨432512747976756580750331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4613469311752070194670197 432512747976756580750331)
    ·
      refine ⟨648769121965134871125497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432512747976756580750331 648769121965134871125497)
      ·
        refine ⟨486576841473851153344123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648769121965134871125497 486576841473851153344123)
        ·
          refine ⟨729865262210776730016185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486576841473851153344123 729865262210776730016185)
          ·
            refine ⟨547398946658082547512139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729865262210776730016185 547398946658082547512139)
            ·
              refine ⟨821098419987123821268209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547398946658082547512139 821098419987123821268209)
              ·
                refine ⟨615823814990342865951157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821098419987123821268209 615823814990342865951157)
                ·
                  refine ⟨57733482655344643682921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615823814990342865951157 57733482655344643682921)
                  ·
                    rfl

theorem cell21_252980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_252980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_252980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_252980 prefixEnd_252980 := by exact prefixLift 252980
  have htrace : WordTrace (prefixWord ++ tailWord_252980) baseStart_252980 baseEnd_252980 := by
    simpa [prefixWord, tailWord_252980, baseEnd_252980] using wordTrace_append hprefix tailTrace_252980
  have hstable : (prefixWord ++ tailWord_252980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252980).length < 2 ^ (prefixWord ++ tailWord_252980).sum := by decide
  have hdescent : baseEnd_252980 < baseStart_252980 := by decide
  rcases family_descends (prefixWord ++ tailWord_252980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253084 : List Nat := [2, 2, 3, 2, 1, 3, 2, 6]
def baseStart_253084 : Nat := 118140960795 + 253084 * 2 ^ 59
def prefixEnd_253084 : Nat := 4983230072969 + 3 ^ 40 * 253084 * 2
def baseEnd_253084 : Nat := 19252405624087857983125

theorem tailTrace_253084 : CollatzResearch.WordTrace tailWord_253084 prefixEnd_253084 19252405624087857983125 := by
  unfold tailWord_253084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615365907563683075563153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6153821210084910767417537 4615365907563683075563153)
  ·
    refine ⟨3461524430672762306672365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4615365907563683075563153 3461524430672762306672365)
    ·
      refine ⟨1298071661502285865002137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3461524430672762306672365 1298071661502285865002137)
      ·
        refine ⟨973553746126714398751603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298071661502285865002137 973553746126714398751603)
        ·
          refine ⟨1460330619190071598127405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973553746126714398751603 1460330619190071598127405)
          ·
            refine ⟨547623982196276849297777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1460330619190071598127405 547623982196276849297777)
            ·
              refine ⟨410717986647207636973333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547623982196276849297777 410717986647207636973333)
              ·
                refine ⟨19252405624087857983125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 410717986647207636973333 19252405624087857983125)
                ·
                  rfl

theorem cell21_253084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_253084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253084 prefixEnd_253084 := by exact prefixLift 253084
  have htrace : WordTrace (prefixWord ++ tailWord_253084) baseStart_253084 baseEnd_253084 := by
    simpa [prefixWord, tailWord_253084, baseEnd_253084] using wordTrace_append hprefix tailTrace_253084
  have hstable : (prefixWord ++ tailWord_253084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253084).length < 2 ^ (prefixWord ++ tailWord_253084).sum := by decide
  have hdescent : baseEnd_253084 < baseStart_253084 := by decide
  rcases family_descends (prefixWord ++ tailWord_253084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253112 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_253112 : Nat := 118140960795 + 253112 * 2 ^ 59
def prefixEnd_253112 : Nat := 4983230072969 + 3 ^ 40 * 253112 * 2
def baseEnd_253112 : Nat := 57763606853741747482651

theorem tailTrace_253112 : CollatzResearch.WordTrace tailWord_253112 prefixEnd_253112 57763606853741747482651 := by
  unfold tailWord_253112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615876529512963466572795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6154502039350617955430393 4615876529512963466572795)
  ·
    refine ⟨6923814794269445199859193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4615876529512963466572795 6923814794269445199859193)
    ·
      refine ⟨5192861095702083899894395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923814794269445199859193 5192861095702083899894395)
      ·
        refine ⟨7789291643553125849841593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192861095702083899894395 7789291643553125849841593)
        ·
          refine ⟨5841968732664844387381195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7789291643553125849841593 5841968732664844387381195)
          ·
            refine ⟨8762953098997266581071793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841968732664844387381195 8762953098997266581071793)
            ·
              refine ⟨6572214824247949935803845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8762953098997266581071793 6572214824247949935803845)
              ·
                refine ⟨1232290279546490612963221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6572214824247949935803845 1232290279546490612963221)
                ·
                  refine ⟨57763606853741747482651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1232290279546490612963221 57763606853741747482651)
                  ·
                    rfl

theorem cell21_253112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_253112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253112 prefixEnd_253112 := by exact prefixLift 253112
  have htrace : WordTrace (prefixWord ++ tailWord_253112) baseStart_253112 baseEnd_253112 := by
    simpa [prefixWord, tailWord_253112, baseEnd_253112] using wordTrace_append hprefix tailTrace_253112
  have hstable : (prefixWord ++ tailWord_253112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253112).length < 2 ^ (prefixWord ++ tailWord_253112).sum := by decide
  have hdescent : baseEnd_253112 < baseStart_253112 := by decide
  rcases family_descends (prefixWord ++ tailWord_253112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253143 : List Nat := [1, 1, 3, 2, 1, 2, 5, 6]
def baseStart_253143 : Nat := 118140960795 + 253143 * 2 ^ 59
def prefixEnd_253143 : Nat := 4983230072969 + 3 ^ 40 * 253143 * 2
def baseEnd_253143 : Nat := 19256893825364194155307

theorem tailTrace_253143 : CollatzResearch.WordTrace tailWord_253143 prefixEnd_253143 19256893825364194155307 := by
  unfold tailWord_253143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232883721913619227524083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6155255814609079485016055 9232883721913619227524083)
  ·
    refine ⟨13849325582870428841286125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9232883721913619227524083 13849325582870428841286125)
    ·
      refine ⟨5193497093576410815482297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13849325582870428841286125 5193497093576410815482297)
      ·
        refine ⟨3895122820182308111611723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5193497093576410815482297 3895122820182308111611723)
        ·
          refine ⟨5842684230273462167417585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895122820182308111611723 5842684230273462167417585)
          ·
            refine ⟨4382013172705096625563189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5842684230273462167417585 4382013172705096625563189)
            ·
              refine ⟨410813734941102808646549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4382013172705096625563189 410813734941102808646549)
              ·
                refine ⟨19256893825364194155307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 410813734941102808646549 19256893825364194155307)
                ·
                  rfl

theorem cell21_253143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_253143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253143 prefixEnd_253143 := by exact prefixLift 253143
  have htrace : WordTrace (prefixWord ++ tailWord_253143) baseStart_253143 baseEnd_253143 := by
    simpa [prefixWord, tailWord_253143, baseEnd_253143] using wordTrace_append hprefix tailTrace_253143
  have hstable : (prefixWord ++ tailWord_253143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253143).length < 2 ^ (prefixWord ++ tailWord_253143).sum := by decide
  have hdescent : baseEnd_253143 < baseStart_253143 := by decide
  rcases family_descends (prefixWord ++ tailWord_253143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253160 : List Nat := [2, 1, 4, 1, 2, 1, 5, 5]
def baseStart_253160 : Nat := 118140960795 + 253160 * 2 ^ 59
def prefixEnd_253160 : Nat := 4983230072969 + 3 ^ 40 * 253160 * 2
def baseEnd_253160 : Nat := 19258187035901443560851

theorem tailTrace_253160 : CollatzResearch.WordTrace tailWord_253160 prefixEnd_253160 19258187035901443560851 := by
  unfold tailWord_253160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616751881426015565446467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6155669175234687420595289 4616751881426015565446467)
  ·
    refine ⟨6925127822139023348169701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4616751881426015565446467 6925127822139023348169701)
    ·
      refine ⟨1298461466651066877781819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6925127822139023348169701 1298461466651066877781819)
      ·
        refine ⟨1947692199976600316672729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298461466651066877781819 1947692199976600316672729)
        ·
          refine ⟨1460769149982450237504547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1947692199976600316672729 1460769149982450237504547)
          ·
            refine ⟨2191153724973675356256821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460769149982450237504547 2191153724973675356256821)
            ·
              refine ⟨205420661716282064649077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2191153724973675356256821 205420661716282064649077)
              ·
                refine ⟨19258187035901443560851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205420661716282064649077 19258187035901443560851)
                ·
                  rfl

theorem cell21_253160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_253160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253160 prefixEnd_253160 := by exact prefixLift 253160
  have htrace : WordTrace (prefixWord ++ tailWord_253160) baseStart_253160 baseEnd_253160 := by
    simpa [prefixWord, tailWord_253160, baseEnd_253160] using wordTrace_append hprefix tailTrace_253160
  have hstable : (prefixWord ++ tailWord_253160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253160).length < 2 ^ (prefixWord ++ tailWord_253160).sum := by decide
  have hdescent : baseEnd_253160 < baseStart_253160 := by decide
  rcases family_descends (prefixWord ++ tailWord_253160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253174 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_253174 : Nat := 118140960795 + 253174 * 2 ^ 59
def prefixEnd_253174 : Nat := 4983230072969 + 3 ^ 40 * 253174 * 2
def baseEnd_253174 : Nat := 57777756098443417449191

theorem tailTrace_253174 : CollatzResearch.WordTrace tailWord_253174 prefixEnd_253174 57777756098443417449191 := by
  unfold tailWord_253174
  simp only [CollatzResearch.WordTrace]
  refine ⟨577125899050081970118911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6156009589867541014601717 577125899050081970118911)
  ·
    refine ⟨865688848575122955178367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577125899050081970118911 865688848575122955178367)
    ·
      refine ⟨1298533272862684432767551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865688848575122955178367 1298533272862684432767551)
      ·
        refine ⟨1947799909294026649151327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298533272862684432767551 1947799909294026649151327)
        ·
          refine ⟨2921699863941039973726991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947799909294026649151327 2921699863941039973726991)
          ·
            refine ⟨4382549795911559960590487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921699863941039973726991 4382549795911559960590487)
            ·
              refine ⟨6573824693867339940885731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382549795911559960590487 6573824693867339940885731)
              ·
                refine ⟨9860737040801009911328597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573824693867339940885731 9860737040801009911328597)
                ·
                  refine ⟨57777756098443417449191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9860737040801009911328597 57777756098443417449191)
                  ·
                    rfl

theorem cell21_253174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_253174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253174 prefixEnd_253174 := by exact prefixLift 253174
  have htrace : WordTrace (prefixWord ++ tailWord_253174) baseStart_253174 baseEnd_253174 := by
    simpa [prefixWord, tailWord_253174, baseEnd_253174] using wordTrace_append hprefix tailTrace_253174
  have hstable : (prefixWord ++ tailWord_253174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253174).length < 2 ^ (prefixWord ++ tailWord_253174).sum := by decide
  have hdescent : baseEnd_253174 < baseStart_253174 := by decide
  rcases family_descends (prefixWord ++ tailWord_253174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253219 : List Nat := [1, 1, 1, 4, 2, 4, 1, 7]
def baseStart_253219 : Nat := 118140960795 + 253219 * 2 ^ 59
def prefixEnd_253219 : Nat := 4983230072969 + 3 ^ 40 * 253219 * 2
def baseEnd_253219 : Nat := 19262675237177779733033

theorem tailTrace_253219 : CollatzResearch.WordTrace tailWord_253219 prefixEnd_253219 19262675237177779733033 := by
  unfold tailWord_253219
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235655669638284207290711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6157103779758856138193807 9235655669638284207290711)
  ·
    refine ⟨13853483504457426310936067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235655669638284207290711 13853483504457426310936067)
    ·
      refine ⟨20780225256686139466404101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13853483504457426310936067 20780225256686139466404101)
      ·
        refine ⟨3896292235628651149950769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20780225256686139466404101 3896292235628651149950769)
        ·
          refine ⟨2922219176721488362463077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896292235628651149950769 2922219176721488362463077)
          ·
            refine ⟨547916095635279067961827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2922219176721488362463077 547916095635279067961827)
            ·
              refine ⟨821874143452918601942741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547916095635279067961827 821874143452918601942741)
              ·
                refine ⟨19262675237177779733033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 821874143452918601942741 19262675237177779733033)
                ·
                  rfl

theorem cell21_253219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_253219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253219 prefixEnd_253219 := by exact prefixLift 253219
  have htrace : WordTrace (prefixWord ++ tailWord_253219) baseStart_253219 baseEnd_253219 := by
    simpa [prefixWord, tailWord_253219, baseEnd_253219] using wordTrace_append hprefix tailTrace_253219
  have hstable : (prefixWord ++ tailWord_253219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253219).length < 2 ^ (prefixWord ++ tailWord_253219).sum := by decide
  have hdescent : baseEnd_253219 < baseStart_253219 := by decide
  rcases family_descends (prefixWord ++ tailWord_253219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253343 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 3]
def baseStart_253343 : Nat := 118140960795 + 253343 * 2 ^ 59
def prefixEnd_253343 : Nat := 4983230072969 + 3 ^ 40 * 253343 * 2
def baseEnd_253343 : Nat := 57816324200936679132179

theorem tailTrace_253343 : CollatzResearch.WordTrace tailWord_253343 prefixEnd_253343 57816324200936679132179 := by
  unfold tailWord_253343
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240178321189053384804683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6160118880792702256536455 9240178321189053384804683)
  ·
    refine ⟨13860267481783580077207025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9240178321189053384804683 13860267481783580077207025)
    ·
      refine ⟨10395200611337685057905269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13860267481783580077207025 10395200611337685057905269)
      ·
        refine ⟨974550057312907974178619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10395200611337685057905269 974550057312907974178619)
        ·
          refine ⟨1461825085969361961267929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974550057312907974178619 1461825085969361961267929)
          ·
            refine ⟨1096368814477021470950947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461825085969361961267929 1096368814477021470950947)
            ·
              refine ⟨1644553221715532206426421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096368814477021470950947 1644553221715532206426421)
              ·
                refine ⟨154176864535831144352477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1644553221715532206426421 154176864535831144352477)
                ·
                  refine ⟨57816324200936679132179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154176864535831144352477 57816324200936679132179)
                  ·
                    rfl

theorem cell21_253343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3].length) (baseStart_253343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253343 prefixEnd_253343 := by exact prefixLift 253343
  have htrace : WordTrace (prefixWord ++ tailWord_253343) baseStart_253343 baseEnd_253343 := by
    simpa [prefixWord, tailWord_253343, baseEnd_253343] using wordTrace_append hprefix tailTrace_253343
  have hstable : (prefixWord ++ tailWord_253343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253343).length < 2 ^ (prefixWord ++ tailWord_253343).sum := by decide
  have hdescent : baseEnd_253343 < baseStart_253343 := by decide
  rcases family_descends (prefixWord ++ tailWord_253343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253388 : List Nat := [2, 2, 1, 4, 2, 1, 4, 5]
def baseStart_253388 : Nat := 118140960795 + 253388 * 2 ^ 59
def prefixEnd_253388 : Nat := 4983230072969 + 3 ^ 40 * 253388 * 2
def baseEnd_253388 : Nat := 19275531271342200294029

theorem tailTrace_253388 : CollatzResearch.WordTrace tailWord_253388 prefixEnd_253388 19275531271342200294029 := by
  unfold tailWord_253388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620909803013013035096409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6161213070684017380128545 4620909803013013035096409)
  ·
    refine ⟨3465682352259759776322307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4620909803013013035096409 3465682352259759776322307)
    ·
      refine ⟨5198523528389639664483461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465682352259759776322307 5198523528389639664483461)
      ·
        refine ⟨974723161573057437090649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5198523528389639664483461 974723161573057437090649)
        ·
          refine ⟨731042371179793077817987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974723161573057437090649 731042371179793077817987)
          ·
            refine ⟨1096563556769689616726981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731042371179793077817987 1096563556769689616726981)
            ·
              refine ⟨205605666894316803136309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096563556769689616726981 205605666894316803136309)
              ·
                refine ⟨19275531271342200294029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205605666894316803136309 19275531271342200294029)
                ·
                  rfl

theorem cell21_253388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_253388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253388 prefixEnd_253388 := by exact prefixLift 253388
  have htrace : WordTrace (prefixWord ++ tailWord_253388) baseStart_253388 baseEnd_253388 := by
    simpa [prefixWord, tailWord_253388, baseEnd_253388] using wordTrace_append hprefix tailTrace_253388
  have hstable : (prefixWord ++ tailWord_253388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253388).length < 2 ^ (prefixWord ++ tailWord_253388).sum := by decide
  have hdescent : baseEnd_253388 < baseStart_253388 := by decide
  rcases family_descends (prefixWord ++ tailWord_253388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253416 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_253416 : Nat := 118140960795 + 253416 * 2 ^ 59
def prefixEnd_253416 : Nat := 4983230072969 + 3 ^ 40 * 253416 * 2
def baseEnd_253416 : Nat := 57832983795504774415363

theorem tailTrace_253416 : CollatzResearch.WordTrace tailWord_253416 prefixEnd_253416 57832983795504774415363 := by
  unfold tailWord_253416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621420424962293426106051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6161893899949724568141401 4621420424962293426106051)
  ·
    refine ⟨6932130637443440139159077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621420424962293426106051 6932130637443440139159077)
    ·
      refine ⟨1299774494520645026092327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6932130637443440139159077 1299774494520645026092327)
      ·
        refine ⟨1949661741780967539138491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299774494520645026092327 1949661741780967539138491)
        ·
          refine ⟨2924492612671451308707737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949661741780967539138491 2924492612671451308707737)
          ·
            refine ⟨2193369459503588481530803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924492612671451308707737 2193369459503588481530803)
            ·
              refine ⟨3290054189255382722296205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193369459503588481530803 3290054189255382722296205)
              ·
                refine ⟨1233770320970768520861077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3290054189255382722296205 1233770320970768520861077)
                ·
                  refine ⟨57832983795504774415363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1233770320970768520861077 57832983795504774415363)
                  ·
                    rfl

theorem cell21_253416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_253416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253416 prefixEnd_253416 := by exact prefixLift 253416
  have htrace : WordTrace (prefixWord ++ tailWord_253416) baseStart_253416 baseEnd_253416 := by
    simpa [prefixWord, tailWord_253416, baseEnd_253416] using wordTrace_append hprefix tailTrace_253416
  have hstable : (prefixWord ++ tailWord_253416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253416).length < 2 ^ (prefixWord ++ tailWord_253416).sum := by decide
  have hdescent : baseEnd_253416 < baseStart_253416 := by decide
  rcases family_descends (prefixWord ++ tailWord_253416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253447 : List Nat := [1, 1, 4, 3, 2, 1, 2, 7]
def baseStart_253447 : Nat := 118140960795 + 253447 * 2 ^ 59
def prefixEnd_253447 : Nat := 4983230072969 + 3 ^ 40 * 253447 * 2
def baseEnd_253447 : Nat := 19280019472618536466211

theorem tailTrace_253447 : CollatzResearch.WordTrace tailWord_253447 prefixEnd_253447 19280019472618536466211 := by
  unfold tailWord_253447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243971512812279146590595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6162647675208186097727063 9243971512812279146590595)
  ·
    refine ⟨13865957269218418719885893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9243971512812279146590595 13865957269218418719885893)
    ·
      refine ⟨2599866987978453509978605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13865957269218418719885893 2599866987978453509978605)
      ·
        refine ⟨974950120491920066241977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2599866987978453509978605 974950120491920066241977)
        ·
          refine ⟨731212590368940049681483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974950120491920066241977 731212590368940049681483)
          ·
            refine ⟨1096818885553410074522225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731212590368940049681483 1096818885553410074522225)
            ·
              refine ⟨822614164165057555891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096818885553410074522225 822614164165057555891669)
              ·
                refine ⟨19280019472618536466211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 822614164165057555891669 19280019472618536466211)
                ·
                  rfl

theorem cell21_253447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_253447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253447 prefixEnd_253447 := by exact prefixLift 253447
  have htrace : WordTrace (prefixWord ++ tailWord_253447) baseStart_253447 baseEnd_253447 := by
    simpa [prefixWord, tailWord_253447, baseEnd_253447] using wordTrace_append hprefix tailTrace_253447
  have hstable : (prefixWord ++ tailWord_253447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253447).length < 2 ^ (prefixWord ++ tailWord_253447).sum := by decide
  have hdescent : baseEnd_253447 < baseStart_253447 := by decide
  rcases family_descends (prefixWord ++ tailWord_253447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253554 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_253554 : Nat := 118140960795 + 253554 * 2 ^ 59
def prefixEnd_253554 : Nat := 4983230072969 + 3 ^ 40 * 253554 * 2
def baseEnd_253554 : Nat := 57864477275647201115081

theorem tailTrace_253554 : CollatzResearch.WordTrace tailWord_253554 prefixEnd_253554 57864477275647201115081 := by
  unfold tailWord_253554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311968530856159105183929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6165249415616424280490477 2311968530856159105183929)
  ·
    refine ⟨1733976398142119328887947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2311968530856159105183929 1733976398142119328887947)
    ·
      refine ⟨2600964597213178993331921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733976398142119328887947 2600964597213178993331921)
      ·
        refine ⟨1950723447909884244998941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2600964597213178993331921 1950723447909884244998941)
        ·
          refine ⟨731521292966206591874603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1950723447909884244998941 731521292966206591874603)
          ·
            refine ⟨1097281939449309887811905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731521292966206591874603 1097281939449309887811905)
            ·
              refine ⟨822961454586982415858929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097281939449309887811905 822961454586982415858929)
              ·
                refine ⟨617221090940236811894197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822961454586982415858929 617221090940236811894197)
                ·
                  refine ⟨57864477275647201115081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617221090940236811894197 57864477275647201115081)
                  ·
                    rfl

theorem cell21_253554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_253554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253554 prefixEnd_253554 := by exact prefixLift 253554
  have htrace : WordTrace (prefixWord ++ tailWord_253554) baseStart_253554 baseEnd_253554 := by
    simpa [prefixWord, tailWord_253554, baseEnd_253554] using wordTrace_append hprefix tailTrace_253554
  have hstable : (prefixWord ++ tailWord_253554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253554).length < 2 ^ (prefixWord ++ tailWord_253554).sum := by decide
  have hdescent : baseEnd_253554 < baseStart_253554 := by decide
  rcases family_descends (prefixWord ++ tailWord_253554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253557 : List Nat := [1, 3, 4, 2, 1, 3, 2, 5]
def baseStart_253557 : Nat := 118140960795 + 253557 * 2 ^ 59
def prefixEnd_253557 : Nat := 4983230072969 + 3 ^ 40 * 253557 * 2
def baseEnd_253557 : Nat := 19288387305506620855025

theorem tailTrace_253557 : CollatzResearch.WordTrace tailWord_253557 prefixEnd_253557 19288387305506620855025 := by
  unfold tailWord_253557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247983542413767933094925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6165322361609178622063283 9247983542413767933094925)
  ·
    refine ⟨3467993828405162974910597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9247983542413767933094925 3467993828405162974910597)
    ·
      refine ⟨650248842825968057795737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3467993828405162974910597 650248842825968057795737)
      ·
        refine ⟨487686632119476043346803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650248842825968057795737 487686632119476043346803)
        ·
          refine ⟨731529948179214065020205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487686632119476043346803 731529948179214065020205)
          ·
            refine ⟨274323730567205274382577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731529948179214065020205 274323730567205274382577)
            ·
              refine ⟨205742797925403955786933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274323730567205274382577 205742797925403955786933)
              ·
                refine ⟨19288387305506620855025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205742797925403955786933 19288387305506620855025)
                ·
                  rfl

theorem cell21_253557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 5].length) (baseStart_253557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253557 prefixEnd_253557 := by exact prefixLift 253557
  have htrace : WordTrace (prefixWord ++ tailWord_253557) baseStart_253557 baseEnd_253557 := by
    simpa [prefixWord, tailWord_253557, baseEnd_253557] using wordTrace_append hprefix tailTrace_253557
  have hstable : (prefixWord ++ tailWord_253557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253557).length < 2 ^ (prefixWord ++ tailWord_253557).sum := by decide
  have hdescent : baseEnd_253557 < baseStart_253557 := by decide
  rcases family_descends (prefixWord ++ tailWord_253557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253588 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_253588 : Nat := 118140960795 + 253588 * 2 ^ 59
def prefixEnd_253588 : Nat := 4983230072969 + 3 ^ 40 * 253588 * 2
def baseEnd_253588 : Nat := 57872236538870697548345

theorem tailTrace_253588 : CollatzResearch.WordTrace tailWord_253588 prefixEnd_253588 57872236538870697548345 := by
  unfold tailWord_253588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624557102650730113736709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6166076136867640151648945 4624557102650730113736709)
  ·
    refine ⟨867104456747011896325633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4624557102650730113736709 867104456747011896325633)
    ·
      refine ⟨650328342560258922244225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867104456747011896325633 650328342560258922244225)
      ·
        refine ⟨487746256920194191683169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650328342560258922244225 487746256920194191683169)
        ·
          refine ⟨365809692690145643762377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487746256920194191683169 365809692690145643762377)
          ·
            refine ⟨274357269517609232821783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365809692690145643762377 274357269517609232821783)
            ·
              refine ⟨411535904276413849232675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274357269517609232821783 411535904276413849232675)
              ·
                refine ⟨617303856414620773849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411535904276413849232675 617303856414620773849013)
                ·
                  refine ⟨57872236538870697548345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617303856414620773849013 57872236538870697548345)
                  ·
                    rfl

theorem cell21_253588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_253588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253588 prefixEnd_253588 := by exact prefixLift 253588
  have htrace : WordTrace (prefixWord ++ tailWord_253588) baseStart_253588 baseEnd_253588 := by
    simpa [prefixWord, tailWord_253588, baseEnd_253588] using wordTrace_append hprefix tailTrace_253588
  have hstable : (prefixWord ++ tailWord_253588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253588).length < 2 ^ (prefixWord ++ tailWord_253588).sum := by decide
  have hdescent : baseEnd_253588 < baseStart_253588 := by decide
  rcases family_descends (prefixWord ++ tailWord_253588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253627 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_253627 : Nat := 118140960795 + 253627 * 2 ^ 59
def prefixEnd_253627 : Nat := 4983230072969 + 3 ^ 40 * 253627 * 2
def baseEnd_253627 : Nat := 57881136870215296398265

theorem tailTrace_253627 : CollatzResearch.WordTrace tailWord_253627 prefixEnd_253627 57881136870215296398265 := by
  unfold tailWord_253627
  simp only [CollatzResearch.WordTrace]
  refine ⟨9250536652160169888143135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6167024434773446592095423 9250536652160169888143135)
  ·
    refine ⟨13875804978240254832214703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9250536652160169888143135 13875804978240254832214703)
    ·
      refine ⟨20813707467360382248322055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13875804978240254832214703 20813707467360382248322055)
      ·
        refine ⟨31220561201040573372483083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20813707467360382248322055 31220561201040573372483083)
        ·
          refine ⟨46830841801560860058724625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31220561201040573372483083 46830841801560860058724625)
          ·
            refine ⟨35123131351170645044043469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46830841801560860058724625 35123131351170645044043469)
            ·
              refine ⟨13171174256688991891516301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35123131351170645044043469 13171174256688991891516301)
              ·
                refine ⟨4939190346258371959318613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13171174256688991891516301 4939190346258371959318613)
                ·
                  refine ⟨57881136870215296398265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4939190346258371959318613 57881136870215296398265)
                  ·
                    rfl

theorem cell21_253627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_253627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253627 prefixEnd_253627 := by exact prefixLift 253627
  have htrace : WordTrace (prefixWord ++ tailWord_253627) baseStart_253627 baseEnd_253627 := by
    simpa [prefixWord, tailWord_253627, baseEnd_253627] using wordTrace_append hprefix tailTrace_253627
  have hstable : (prefixWord ++ tailWord_253627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253627).length < 2 ^ (prefixWord ++ tailWord_253627).sum := by decide
  have hdescent : baseEnd_253627 < baseStart_253627 := by decide
  rcases family_descends (prefixWord ++ tailWord_253627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253706 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_253706 : Nat := 118140960795 + 253706 * 2 ^ 59
def prefixEnd_253706 : Nat := 4983230072969 + 3 ^ 40 * 253706 * 2
def baseEnd_253706 : Nat := 57899165746528714581437

theorem tailTrace_253706 : CollatzResearch.WordTrace tailWord_253706 prefixEnd_253706 57899165746528714581437 := by
  unfold tailWord_253706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313354504718491595067243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6168945345915977586845981 2313354504718491595067243)
  ·
    refine ⟨3470031757077737392600865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2313354504718491595067243 3470031757077737392600865)
    ·
      refine ⟨2602523817808303044450649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3470031757077737392600865 2602523817808303044450649)
      ·
        refine ⟨1951892863356227283337987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2602523817808303044450649 1951892863356227283337987)
        ·
          refine ⟨2927839295034340925006981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951892863356227283337987 2927839295034340925006981)
          ·
            refine ⟨548969867818938923438809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2927839295034340925006981 548969867818938923438809)
            ·
              refine ⟨411727400864204192579107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548969867818938923438809 411727400864204192579107)
              ·
                refine ⟨617591101296306288868661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411727400864204192579107 617591101296306288868661)
                ·
                  refine ⟨57899165746528714581437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 617591101296306288868661 57899165746528714581437)
                  ·
                    rfl

theorem cell21_253706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_253706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253706 prefixEnd_253706 := by exact prefixLift 253706
  have htrace : WordTrace (prefixWord ++ tailWord_253706) baseStart_253706 baseEnd_253706 := by
    simpa [prefixWord, tailWord_253706, baseEnd_253706] using wordTrace_append hprefix tailTrace_253706
  have hstable : (prefixWord ++ tailWord_253706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253706).length < 2 ^ (prefixWord ++ tailWord_253706).sum := by decide
  have hdescent : baseEnd_253706 < baseStart_253706 := by decide
  rcases family_descends (prefixWord ++ tailWord_253706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253720 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_253720 : Nat := 118140960795 + 253720 * 2 ^ 59
def prefixEnd_253720 : Nat := 4983230072969 + 3 ^ 40 * 253720 * 2
def baseEnd_253720 : Nat := 57902360737267801348075

theorem tailTrace_253720 : CollatzResearch.WordTrace tailWord_253720 prefixEnd_253720 57902360737267801348075 := by
  unfold tailWord_253720
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626964320411623385639307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6169285760548831180852409 4626964320411623385639307)
  ·
    refine ⟨6940446480617435078458961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4626964320411623385639307 6940446480617435078458961)
    ·
      refine ⟨5205334860463076308844221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6940446480617435078458961 5205334860463076308844221)
      ·
        refine ⟨1952000572673653615816583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5205334860463076308844221 1952000572673653615816583)
        ·
          refine ⟨2928000859010480423724875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952000572673653615816583 2928000859010480423724875)
          ·
            refine ⟨4392001288515720635587313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928000859010480423724875 4392001288515720635587313)
            ·
              refine ⟨3294000966386790476690485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392001288515720635587313 3294000966386790476690485)
              ·
                refine ⟨308812590598761607189733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3294000966386790476690485 308812590598761607189733)
                ·
                  refine ⟨57902360737267801348075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308812590598761607189733 57902360737267801348075)
                  ·
                    rfl

theorem cell21_253720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_253720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253720 prefixEnd_253720 := by exact prefixLift 253720
  have htrace : WordTrace (prefixWord ++ tailWord_253720) baseStart_253720 baseEnd_253720 := by
    simpa [prefixWord, tailWord_253720, baseEnd_253720] using wordTrace_append hprefix tailTrace_253720
  have hstable : (prefixWord ++ tailWord_253720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253720).length < 2 ^ (prefixWord ++ tailWord_253720).sum := by decide
  have hdescent : baseEnd_253720 < baseStart_253720 := by decide
  rcases family_descends (prefixWord ++ tailWord_253720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253813 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 4]
def baseStart_253813 : Nat := 118140960795 + 253813 * 2 ^ 59
def prefixEnd_253813 : Nat := 4983230072969 + 3 ^ 40 * 253813 * 2
def baseEnd_253813 : Nat := 57923584604320306297885

theorem tailTrace_253813 : CollatzResearch.WordTrace tailWord_253813 prefixEnd_253813 57923584604320306297885 := by
  unfold tailWord_253813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257320629486323654414093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6171547086324215769609395 9257320629486323654414093)
  ·
    refine ⟨3471495236057371370405285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9257320629486323654414093 3471495236057371370405285)
    ·
      refine ⟨650905356760757131950991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3471495236057371370405285 650905356760757131950991)
      ·
        refine ⟨976358035141135697926487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650905356760757131950991 976358035141135697926487)
        ·
          refine ⟨1464537052711703546889731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976358035141135697926487 1464537052711703546889731)
          ·
            refine ⟨2196805579067555320334597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464537052711703546889731 2196805579067555320334597)
            ·
              refine ⟨411901046075166622562737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2196805579067555320334597 411901046075166622562737)
              ·
                refine ⟨308925784556374966922053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411901046075166622562737 308925784556374966922053)
                ·
                  refine ⟨57923584604320306297885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308925784556374966922053 57923584604320306297885)
                  ·
                    rfl

theorem cell21_253813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_253813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253813 prefixEnd_253813 := by exact prefixLift 253813
  have htrace : WordTrace (prefixWord ++ tailWord_253813) baseStart_253813 baseEnd_253813 := by
    simpa [prefixWord, tailWord_253813, baseEnd_253813] using wordTrace_append hprefix tailTrace_253813
  have hstable : (prefixWord ++ tailWord_253813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253813).length < 2 ^ (prefixWord ++ tailWord_253813).sum := by decide
  have hdescent : baseEnd_253813 < baseStart_253813 := by decide
  rcases family_descends (prefixWord ++ tailWord_253813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253827 : List Nat := [1, 1, 1, 3, 4, 4, 1, 6]
def baseStart_253827 : Nat := 118140960795 + 253827 * 2 ^ 59
def prefixEnd_253827 : Nat := 4983230072969 + 3 ^ 40 * 253827 * 2
def baseEnd_253827 : Nat := 19308926531686464354841

theorem tailTrace_253827 : CollatzResearch.WordTrace tailWord_253827 prefixEnd_253827 19308926531686464354841 := by
  unfold tailWord_253827
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257831251435604045423735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6171887500957069363615823 9257831251435604045423735)
  ·
    refine ⟨13886746877153406068135603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9257831251435604045423735 13886746877153406068135603)
    ·
      refine ⟨20830120315730109102203405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886746877153406068135603 20830120315730109102203405)
      ·
        refine ⟨7811295118398790913326277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20830120315730109102203405 7811295118398790913326277)
        ·
          refine ⟨1464617834699773296248677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7811295118398790913326277 1464617834699773296248677)
          ·
            refine ⟨274615844006207493046627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1464617834699773296248677 274615844006207493046627)
            ·
              refine ⟨411923766009311239569941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274615844006207493046627 411923766009311239569941)
              ·
                refine ⟨19308926531686464354841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 411923766009311239569941 19308926531686464354841)
                ·
                  rfl

theorem cell21_253827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 6].length) (baseStart_253827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253827 prefixEnd_253827 := by exact prefixLift 253827
  have htrace : WordTrace (prefixWord ++ tailWord_253827) baseStart_253827 baseEnd_253827 := by
    simpa [prefixWord, tailWord_253827, baseEnd_253827] using wordTrace_append hprefix tailTrace_253827
  have hstable : (prefixWord ++ tailWord_253827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253827).length < 2 ^ (prefixWord ++ tailWord_253827).sum := by decide
  have hdescent : baseEnd_253827 < baseStart_253827 := by decide
  rcases family_descends (prefixWord ++ tailWord_253827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253844 : List Nat := [2, 4, 2, 1, 1, 3, 3, 5]
def baseStart_253844 : Nat := 118140960795 + 253844 * 2 ^ 59
def prefixEnd_253844 : Nat := 4983230072969 + 3 ^ 40 * 253844 * 2
def baseEnd_253844 : Nat := 19310219742223713760385

theorem tailTrace_253844 : CollatzResearch.WordTrace tailWord_253844 prefixEnd_253844 19310219742223713760385 := by
  unfold tailWord_253844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629225646187007974396293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6172300861582677299195057 4629225646187007974396293)
  ·
    refine ⟨867979808660063995199305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4629225646187007974396293 867979808660063995199305)
    ·
      refine ⟨650984856495047996399479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867979808660063995199305 650984856495047996399479)
      ·
        refine ⟨976477284742571994599219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650984856495047996399479 976477284742571994599219)
        ·
          refine ⟨1464715927113857991898829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976477284742571994599219 1464715927113857991898829)
          ·
            refine ⟨549268472667696746962061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1464715927113857991898829 549268472667696746962061)
            ·
              refine ⟨205975677250386280110773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549268472667696746962061 205975677250386280110773)
              ·
                refine ⟨19310219742223713760385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205975677250386280110773 19310219742223713760385)
                ·
                  rfl

theorem cell21_253844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_253844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253844 prefixEnd_253844 := by exact prefixLift 253844
  have htrace : WordTrace (prefixWord ++ tailWord_253844) baseStart_253844 baseEnd_253844 := by
    simpa [prefixWord, tailWord_253844, baseEnd_253844] using wordTrace_append hprefix tailTrace_253844
  have hstable : (prefixWord ++ tailWord_253844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253844).length < 2 ^ (prefixWord ++ tailWord_253844).sum := by decide
  have hdescent : baseEnd_253844 < baseStart_253844 := by decide
  rcases family_descends (prefixWord ++ tailWord_253844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253864 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_253864 : Nat := 118140960795 + 253864 * 2 ^ 59
def prefixEnd_253864 : Nat := 4983230072969 + 3 ^ 40 * 253864 * 2
def baseEnd_253864 : Nat := 57935223499155550947781

theorem tailTrace_253864 : CollatzResearch.WordTrace tailWord_253864 prefixEnd_253864 57935223499155550947781 := by
  unfold tailWord_253864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629590376150779682260323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6172787168201039576347097 4629590376150779682260323)
  ·
    refine ⟨6944385564226169523390485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4629590376150779682260323 6944385564226169523390485)
    ·
      refine ⟨325518073323101696408929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6944385564226169523390485 325518073323101696408929)
      ·
        refine ⟨244138554992326272306697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325518073323101696408929 244138554992326272306697)
        ·
          refine ⟨183103916244244704230023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244138554992326272306697 183103916244244704230023)
          ·
            refine ⟨274655874366367056345035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183103916244244704230023 274655874366367056345035)
            ·
              refine ⟨411983811549550584517553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274655874366367056345035 411983811549550584517553)
              ·
                refine ⟨308987858662162938388165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411983811549550584517553 308987858662162938388165)
                ·
                  refine ⟨57935223499155550947781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308987858662162938388165 57935223499155550947781)
                  ·
                    rfl

theorem cell21_253864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_253864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253864 prefixEnd_253864 := by exact prefixLift 253864
  have htrace : WordTrace (prefixWord ++ tailWord_253864) baseStart_253864 baseEnd_253864 := by
    simpa [prefixWord, tailWord_253864, baseEnd_253864] using wordTrace_append hprefix tailTrace_253864
  have hstable : (prefixWord ++ tailWord_253864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253864).length < 2 ^ (prefixWord ++ tailWord_253864).sum := by decide
  have hdescent : baseEnd_253864 < baseStart_253864 := by decide
  rcases family_descends (prefixWord ++ tailWord_253864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253934 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_253934 : Nat := 118140960795 + 253934 * 2 ^ 59
def prefixEnd_253934 : Nat := 4983230072969 + 3 ^ 40 * 253934 * 2
def baseEnd_253934 : Nat := 57951198452850984780971

theorem tailTrace_253934 : CollatzResearch.WordTrace tailWord_253934 prefixEnd_253934 57951198452850984780971 := by
  unfold tailWord_253934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157716732755995164946107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6174489241365307546379237 1157716732755995164946107)
  ·
    refine ⟨1736575099133992747419161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1157716732755995164946107 1736575099133992747419161)
    ·
      refine ⟨1302431324350494560564371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1736575099133992747419161 1302431324350494560564371)
      ·
        refine ⟨1953646986525741840846557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302431324350494560564371 1953646986525741840846557)
        ·
          refine ⟨732617619947153190317459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1953646986525741840846557 732617619947153190317459)
          ·
            refine ⟨1098926429920729785476189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732617619947153190317459 1098926429920729785476189)
            ·
              refine ⟨412097411220273669553571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098926429920729785476189 412097411220273669553571)
              ·
                refine ⟨618146116830410504330357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412097411220273669553571 618146116830410504330357)
                ·
                  refine ⟨57951198452850984780971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618146116830410504330357 57951198452850984780971)
                  ·
                    rfl

theorem cell21_253934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_253934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253934 prefixEnd_253934 := by exact prefixLift 253934
  have htrace : WordTrace (prefixWord ++ tailWord_253934) baseStart_253934 baseEnd_253934 := by
    simpa [prefixWord, tailWord_253934, baseEnd_253934] using wordTrace_append hprefix tailTrace_253934
  have hstable : (prefixWord ++ tailWord_253934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253934).length < 2 ^ (prefixWord ++ tailWord_253934).sum := by decide
  have hdescent : baseEnd_253934 < baseStart_253934 := by decide
  rcases family_descends (prefixWord ++ tailWord_253934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253948 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_253948 : Nat := 118140960795 + 253948 * 2 ^ 59
def prefixEnd_253948 : Nat := 4983230072969 + 3 ^ 40 * 253948 * 2
def baseEnd_253948 : Nat := 57954393443590071547609

theorem tailTrace_253948 : CollatzResearch.WordTrace tailWord_253948 prefixEnd_253948 57954393443590071547609 := by
  unfold tailWord_253948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631122241998620855289249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6174829655998161140385665 4631122241998620855289249)
  ·
    refine ⟨3473341681498965641466937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4631122241998620855289249 3473341681498965641466937)
    ·
      refine ⟨2605006261124224231100203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3473341681498965641466937 2605006261124224231100203)
      ·
        refine ⟨3907509391686336346650305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605006261124224231100203 3907509391686336346650305)
        ·
          refine ⟨2930632043764752259987729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3907509391686336346650305 2930632043764752259987729)
          ·
            refine ⟨2197974032823564194990797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2930632043764752259987729 2197974032823564194990797)
            ·
              refine ⟨824240262308836573121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2197974032823564194990797 824240262308836573121549)
              ·
                refine ⟨309090098365813714920581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824240262308836573121549 309090098365813714920581)
                ·
                  refine ⟨57954393443590071547609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309090098365813714920581 57954393443590071547609)
                  ·
                    rfl

theorem cell21_253948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_253948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253948 prefixEnd_253948 := by exact prefixLift 253948
  have htrace : WordTrace (prefixWord ++ tailWord_253948) baseStart_253948 baseEnd_253948 := by
    simpa [prefixWord, tailWord_253948, baseEnd_253948] using wordTrace_append hprefix tailTrace_253948
  have hstable : (prefixWord ++ tailWord_253948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253948).length < 2 ^ (prefixWord ++ tailWord_253948).sum := by decide
  have hdescent : baseEnd_253948 < baseStart_253948 := by decide
  rcases family_descends (prefixWord ++ tailWord_253948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253985 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 3]
def baseStart_253985 : Nat := 118140960795 + 253985 * 2 ^ 59
def prefixEnd_253985 : Nat := 4983230072969 + 3 ^ 40 * 253985 * 2
def baseEnd_253985 : Nat := 57962837347686229430867

theorem tailTrace_253985 : CollatzResearch.WordTrace tailWord_253985 prefixEnd_253985 57962837347686229430867 := by
  unfold tailWord_253985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263593984863197029675409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6175729323242131353116939 9263593984863197029675409)
  ·
    refine ⟨6947695488647397772256557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9263593984863197029675409 6947695488647397772256557)
    ·
      refine ⟨2605385808242774164596209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6947695488647397772256557 2605385808242774164596209)
      ·
        refine ⟨1954039356182080623447157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2605385808242774164596209 1954039356182080623447157)
        ·
          refine ⟨183191189642070058448171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1954039356182080623447157 183191189642070058448171)
          ·
            refine ⟨274786784463105087672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183191189642070058448171 274786784463105087672257)
            ·
              refine ⟨206090088347328815754193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274786784463105087672257 206090088347328815754193)
              ·
                refine ⟨154567566260496611815645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206090088347328815754193 154567566260496611815645)
                ·
                  refine ⟨57962837347686229430867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154567566260496611815645 57962837347686229430867)
                  ·
                    rfl

theorem cell21_253985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_253985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_253985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_253985 prefixEnd_253985 := by exact prefixLift 253985
  have htrace : WordTrace (prefixWord ++ tailWord_253985) baseStart_253985 baseEnd_253985 := by
    simpa [prefixWord, tailWord_253985, baseEnd_253985] using wordTrace_append hprefix tailTrace_253985
  have hstable : (prefixWord ++ tailWord_253985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253985).length < 2 ^ (prefixWord ++ tailWord_253985).sum := by decide
  have hdescent : baseEnd_253985 < baseStart_253985 := by decide
  rcases family_descends (prefixWord ++ tailWord_253985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254058 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_254058 : Nat := 118140960795 + 254058 * 2 ^ 59
def prefixEnd_254058 : Nat := 4983230072969 + 3 ^ 40 * 254058 * 2
def baseEnd_254058 : Nat := 57979496942254324714051

theorem tailTrace_254058 : CollatzResearch.WordTrace tailWord_254058 prefixEnd_254058 57979496942254324714051 := by
  unfold tailWord_254058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316564128399682624270707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6177504342399153664721885 2316564128399682624270707)
  ·
    refine ⟨3474846192599523936406061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316564128399682624270707 3474846192599523936406061)
    ·
      refine ⟨1303067322224821476152273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3474846192599523936406061 1303067322224821476152273)
      ·
        refine ⟨977300491668616107114205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1303067322224821476152273 977300491668616107114205)
        ·
          refine ⟨366487684375731040167827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 977300491668616107114205 366487684375731040167827)
          ·
            refine ⟨549731526563596560251741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366487684375731040167827 549731526563596560251741)
            ·
              refine ⟨206149322461348710094403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549731526563596560251741 206149322461348710094403)
              ·
                refine ⟨309223983692023065141605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206149322461348710094403 309223983692023065141605)
                ·
                  refine ⟨57979496942254324714051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309223983692023065141605 57979496942254324714051)
                  ·
                    rfl

theorem cell21_254058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_254058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254058 prefixEnd_254058 := by exact prefixLift 254058
  have htrace : WordTrace (prefixWord ++ tailWord_254058) baseStart_254058 baseEnd_254058 := by
    simpa [prefixWord, tailWord_254058, baseEnd_254058] using wordTrace_append hprefix tailTrace_254058
  have hstable : (prefixWord ++ tailWord_254058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254058).length < 2 ^ (prefixWord ++ tailWord_254058).sum := by decide
  have hdescent : baseEnd_254058 < baseStart_254058 := by decide
  rcases family_descends (prefixWord ++ tailWord_254058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254083 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_254083 : Nat := 118140960795 + 254083 * 2 ^ 59
def prefixEnd_254083 : Nat := 4983230072969 + 3 ^ 40 * 254083 * 2
def baseEnd_254083 : Nat := 57985202282859836797333

theorem tailTrace_254083 : CollatzResearch.WordTrace tailWord_254083 prefixEnd_254083 57985202282859836797333 := by
  unfold tailWord_254083
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267168338508159766742903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6178112225672106511161935 9267168338508159766742903)
  ·
    refine ⟨13900752507762239650114355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9267168338508159766742903 13900752507762239650114355)
    ·
      refine ⟨20851128761643359475171533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13900752507762239650114355 20851128761643359475171533)
      ·
        refine ⟨7819173285616259803189325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20851128761643359475171533 7819173285616259803189325)
        ·
          refine ⟨2932189982106097426195997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7819173285616259803189325 2932189982106097426195997)
          ·
            refine ⟨1099571243289786534823499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2932189982106097426195997 1099571243289786534823499)
            ·
              refine ⟨1649356864934679802235249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099571243289786534823499 1649356864934679802235249)
              ·
                refine ⟨1237017648701009851676437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649356864934679802235249 1237017648701009851676437)
                ·
                  refine ⟨57985202282859836797333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1237017648701009851676437 57985202282859836797333)
                  ·
                    rfl

theorem cell21_254083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_254083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254083 prefixEnd_254083 := by exact prefixLift 254083
  have htrace : WordTrace (prefixWord ++ tailWord_254083) baseStart_254083 baseEnd_254083 := by
    simpa [prefixWord, tailWord_254083, baseEnd_254083] using wordTrace_append hprefix tailTrace_254083
  have hstable : (prefixWord ++ tailWord_254083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254083).length < 2 ^ (prefixWord ++ tailWord_254083).sum := by decide
  have hdescent : baseEnd_254083 < baseStart_254083 := by decide
  rcases family_descends (prefixWord ++ tailWord_254083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
