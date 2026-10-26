import V185TrunkScan23Chunk0977

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5789755 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 8]
def baseStart_5789755 : Nat := 118140960795 + 5789755 * 2 ^ 59
def prefixEnd_5789755 : Nat := 4983230072969 + 3 ^ 40 * 5789755 * 2
def baseEnd_5789755 : Nat := 990975728924033430211969

theorem tailTrace_5789755 : CollatzResearch.WordTrace tailWord_5789755 prefixEnd_5789755 990975728924033430211969 := by
  unfold tailWord_5789755
  simp only [CollatzResearch.WordTrace]
  refine ⟨211169713139713921275810719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140779808759809280850540479 211169713139713921275810719)
  ·
    refine ⟨316754569709570881913716079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211169713139713921275810719 316754569709570881913716079)
    ·
      refine ⟨475131854564356322870574119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316754569709570881913716079 475131854564356322870574119)
      ·
        refine ⟨712697781846534484305861179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475131854564356322870574119 712697781846534484305861179)
        ·
          refine ⟨1069046672769801726458791769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712697781846534484305861179 1069046672769801726458791769)
          ·
            refine ⟨801785004577351294844093827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069046672769801726458791769 801785004577351294844093827)
            ·
              refine ⟨1202677506866026942266140741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801785004577351294844093827 1202677506866026942266140741)
              ·
                refine ⟨225502032537380051674901389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1202677506866026942266140741 225502032537380051674901389)
                ·
                  refine ⟨84563262201517519378088021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225502032537380051674901389 84563262201517519378088021)
                  ·
                    refine ⟨990975728924033430211969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84563262201517519378088021 990975728924033430211969)
                    ·
                      rfl

theorem cell23_5789755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_5789755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789755 prefixEnd_5789755 := by exact prefixLift 5789755
  have htrace : WordTrace (prefixWord ++ tailWord_5789755) baseStart_5789755 baseEnd_5789755 := by
    simpa [prefixWord, tailWord_5789755, baseEnd_5789755] using wordTrace_append hprefix tailTrace_5789755
  have hstable : (prefixWord ++ tailWord_5789755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789755).length < 2 ^ (prefixWord ++ tailWord_5789755).sum := by decide
  have hdescent : baseEnd_5789755 < baseStart_5789755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789772 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_5789772 : Nat := 118140960795 + 5789772 * 2 ^ 59
def prefixEnd_5789772 : Nat := 4983230072969 + 3 ^ 40 * 5789772 * 2
def baseEnd_5789772 : Nat := 990978638647742241374443

theorem tailTrace_5789772 : CollatzResearch.WordTrace tailWord_5789772 prefixEnd_5789772 990978638647742241374443 := by
  unfold tailWord_5789772
  simp only [CollatzResearch.WordTrace]
  refine ⟨105585166590326166589589785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140780222120434888786119713 105585166590326166589589785)
  ·
    refine ⟨79188874942744624942192339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105585166590326166589589785 79188874942744624942192339)
    ·
      refine ⟨118783312414116937413288509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79188874942744624942192339 118783312414116937413288509)
      ·
        refine ⟨44543742155293851529983191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118783312414116937413288509 44543742155293851529983191)
        ·
          refine ⟨66815613232940777294974787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44543742155293851529983191 66815613232940777294974787)
          ·
            refine ⟨100223419849411165942462181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66815613232940777294974787 100223419849411165942462181)
            ·
              refine ⟨18791891221764593614211659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100223419849411165942462181 18791891221764593614211659)
              ·
                refine ⟨28187836832646890421317489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18791891221764593614211659 28187836832646890421317489)
                ·
                  refine ⟨21140877624485167815988117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28187836832646890421317489 21140877624485167815988117)
                  ·
                    refine ⟨990978638647742241374443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21140877624485167815988117 990978638647742241374443)
                    ·
                      rfl

theorem cell23_5789772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_5789772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789772 prefixEnd_5789772 := by exact prefixLift 5789772
  have htrace : WordTrace (prefixWord ++ tailWord_5789772) baseStart_5789772 baseEnd_5789772 := by
    simpa [prefixWord, tailWord_5789772, baseEnd_5789772] using wordTrace_append hprefix tailTrace_5789772
  have hstable : (prefixWord ++ tailWord_5789772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789772).length < 2 ^ (prefixWord ++ tailWord_5789772).sum := by decide
  have hdescent : baseEnd_5789772 < baseStart_5789772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789796 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_5789796 : Nat := 118140960795 + 5789796 * 2 ^ 59
def prefixEnd_5789796 : Nat := 4983230072969 + 3 ^ 40 * 5789796 * 2
def baseEnd_5789796 : Nat := 2972948239478934630223219

theorem tailTrace_5789796 : CollatzResearch.WordTrace tailWord_5789796 prefixEnd_5789796 2972948239478934630223219 := by
  unfold tailWord_5789796
  simp only [CollatzResearch.WordTrace]
  refine ⟨105585604266282692639026621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140780805688376923518702161 105585604266282692639026621)
  ·
    refine ⟨39594601599856009739634983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105585604266282692639026621 39594601599856009739634983)
    ·
      refine ⟨59391902399784014609452475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39594601599856009739634983 59391902399784014609452475)
      ·
        refine ⟨89087853599676021914178713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59391902399784014609452475 89087853599676021914178713)
        ·
          refine ⟨66815890199757016435634035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89087853599676021914178713 66815890199757016435634035)
          ·
            refine ⟨100223835299635524653451053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66815890199757016435634035 100223835299635524653451053)
            ·
              refine ⟨37583938237363321745044145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100223835299635524653451053 37583938237363321745044145)
              ·
                refine ⟨28187953678022491308783109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37583938237363321745044145 28187953678022491308783109)
                ·
                  refine ⟨5285241314629217120396833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28187953678022491308783109 5285241314629217120396833)
                  ·
                    refine ⟨3963930985971912840297625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285241314629217120396833 3963930985971912840297625)
                    ·
                      refine ⟨2972948239478934630223219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963930985971912840297625 2972948239478934630223219)
                      ·
                        rfl

theorem cell23_5789796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_5789796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789796 prefixEnd_5789796 := by exact prefixLift 5789796
  have htrace : WordTrace (prefixWord ++ tailWord_5789796) baseStart_5789796 baseEnd_5789796 := by
    simpa [prefixWord, tailWord_5789796, baseEnd_5789796] using wordTrace_append hprefix tailTrace_5789796
  have hstable : (prefixWord ++ tailWord_5789796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789796).length < 2 ^ (prefixWord ++ tailWord_5789796).sum := by decide
  have hdescent : baseEnd_5789796 < baseStart_5789796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789870 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_5789870 : Nat := 118140960795 + 5789870 * 2 ^ 59
def prefixEnd_5789870 : Nat := 4983230072969 + 3 ^ 40 * 5789870 * 2
def baseEnd_5789870 : Nat := 330331804116374148966431

theorem tailTrace_5789870 : CollatzResearch.WordTrace tailWord_5789870 prefixEnd_5789870 330331804116374148966431 := by
  unfold tailWord_5789870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396738441787161989530883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140782605022864863944164709 26396738441787161989530883)
  ·
    refine ⟨39595107662680742984296325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26396738441787161989530883 39595107662680742984296325)
    ·
      refine ⟨7424082686752639309555561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39595107662680742984296325 7424082686752639309555561)
      ·
        refine ⟨5568062015064479482166671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7424082686752639309555561 5568062015064479482166671)
        ·
          refine ⟨8352093022596719223250007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568062015064479482166671 8352093022596719223250007)
          ·
            refine ⟨12528139533895078834875011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8352093022596719223250007 12528139533895078834875011)
            ·
              refine ⟨18792209300842618252312517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12528139533895078834875011 18792209300842618252312517)
              ·
                refine ⟨3523539243907990922308597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18792209300842618252312517 3523539243907990922308597)
                ·
                  refine ⟨330331804116374148966431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523539243907990922308597 330331804116374148966431)
                  ·
                    rfl

theorem cell23_5789870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_5789870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789870 prefixEnd_5789870 := by exact prefixLift 5789870
  have htrace : WordTrace (prefixWord ++ tailWord_5789870) baseStart_5789870 baseEnd_5789870 := by
    simpa [prefixWord, tailWord_5789870, baseEnd_5789870] using wordTrace_append hprefix tailTrace_5789870
  have hstable : (prefixWord ++ tailWord_5789870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789870).length < 2 ^ (prefixWord ++ tailWord_5789870).sum := by decide
  have hdescent : baseEnd_5789870 < baseStart_5789870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789900 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_5789900 : Nat := 118140960795 + 5789900 * 2 ^ 59
def prefixEnd_5789900 : Nat := 4983230072969 + 3 ^ 40 * 5789900 * 2
def baseEnd_5789900 : Nat := 991000547155667407774247

theorem tailTrace_5789900 : CollatzResearch.WordTrace tailWord_5789900 prefixEnd_5789900 991000547155667407774247 := by
  unfold tailWord_5789900
  simp only [CollatzResearch.WordTrace]
  refine ⟨105587500862094305519919577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140783334482792407359892769 105587500862094305519919577)
  ·
    refine ⟨79190625646570729139939683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105587500862094305519919577 79190625646570729139939683)
    ·
      refine ⟨118785938469856093709909525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79190625646570729139939683 118785938469856093709909525)
      ·
        refine ⟨5568090865774504392652009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118785938469856093709909525 5568090865774504392652009)
        ·
          refine ⟨4176068149330878294489007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5568090865774504392652009 4176068149330878294489007)
          ·
            refine ⟨6264102223996317441733511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176068149330878294489007 6264102223996317441733511)
            ·
              refine ⟨9396153335994476162600267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264102223996317441733511 9396153335994476162600267)
              ·
                refine ⟨14094230003991714243900401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396153335994476162600267 14094230003991714243900401)
                ·
                  refine ⟨10570672502993785682925301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14094230003991714243900401 10570672502993785682925301)
                  ·
                    refine ⟨991000547155667407774247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10570672502993785682925301 991000547155667407774247)
                    ·
                      rfl

theorem cell23_5789900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_5789900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789900 prefixEnd_5789900 := by exact prefixLift 5789900
  have htrace : WordTrace (prefixWord ++ tailWord_5789900) baseStart_5789900 baseEnd_5789900 := by
    simpa [prefixWord, tailWord_5789900, baseEnd_5789900] using wordTrace_append hprefix tailTrace_5789900
  have hstable : (prefixWord ++ tailWord_5789900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789900).length < 2 ^ (prefixWord ++ tailWord_5789900).sum := by decide
  have hdescent : baseEnd_5789900 < baseStart_5789900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789906 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_5789906 : Nat := 118140960795 + 5789906 * 2 ^ 59
def prefixEnd_5789906 : Nat := 4983230072969 + 3 ^ 40 * 5789906 * 2
def baseEnd_5789906 : Nat := 2973004722350929199847713

theorem tailTrace_5789906 : CollatzResearch.WordTrace tailWord_5789906 prefixEnd_5789906 2973004722350929199847713 := by
  unfold tailWord_5789906
  simp only [CollatzResearch.WordTrace]
  refine ⟨52793805140541718516139393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140783480374777916043038381 52793805140541718516139393)
  ·
    refine ⟨39595353855406288887104545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52793805140541718516139393 39595353855406288887104545)
    ·
      refine ⟨29696515391554716665328409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39595353855406288887104545 29696515391554716665328409)
      ·
        refine ⟨22272386543666037498996307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29696515391554716665328409 22272386543666037498996307)
        ·
          refine ⟨33408579815499056248494461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22272386543666037498996307 33408579815499056248494461)
          ·
            refine ⟨12528217430812146093185423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33408579815499056248494461 12528217430812146093185423)
            ·
              refine ⟨18792326146218219139778135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12528217430812146093185423 18792326146218219139778135)
              ·
                refine ⟨28188489219327328709667203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18792326146218219139778135 28188489219327328709667203)
                ·
                  refine ⟨42282733828990993064500805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28188489219327328709667203 42282733828990993064500805)
                  ·
                    refine ⟨7928012592935811199593901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42282733828990993064500805 7928012592935811199593901)
                    ·
                      refine ⟨2973004722350929199847713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928012592935811199593901 2973004722350929199847713)
                      ·
                        rfl

theorem cell23_5789906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_5789906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789906 prefixEnd_5789906 := by exact prefixLift 5789906
  have htrace : WordTrace (prefixWord ++ tailWord_5789906) baseStart_5789906 baseEnd_5789906 := by
    simpa [prefixWord, tailWord_5789906, baseEnd_5789906] using wordTrace_append hprefix tailTrace_5789906
  have hstable : (prefixWord ++ tailWord_5789906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789906).length < 2 ^ (prefixWord ++ tailWord_5789906).sum := by decide
  have hdescent : baseEnd_5789906 < baseStart_5789906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789946 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_5789946 : Nat := 118140960795 + 5789946 * 2 ^ 59
def prefixEnd_5789946 : Nat := 4983230072969 + 3 ^ 40 * 5789946 * 2
def baseEnd_5789946 : Nat := 2973025261577109043347529

theorem tailTrace_5789946 : CollatzResearch.WordTrace tailWord_5789946 prefixEnd_5789946 2973025261577109043347529 := by
  unfold tailWord_5789946
  simp only [CollatzResearch.WordTrace]
  refine ⟨52794169870505490224003423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140784452988014640597342461 52794169870505490224003423)
  ·
    refine ⟨79191254805758235336005135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52794169870505490224003423 79191254805758235336005135)
    ·
      refine ⟨118786882208637353004007703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79191254805758235336005135 118786882208637353004007703)
      ·
        refine ⟨178180323312956029506011555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118786882208637353004007703 178180323312956029506011555)
        ·
          refine ⟨267270484969434044259017333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178180323312956029506011555 267270484969434044259017333)
          ·
            refine ⟨25056607965884441649282875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267270484969434044259017333 25056607965884441649282875)
            ·
              refine ⟨37584911948826662473924313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25056607965884441649282875 37584911948826662473924313)
              ·
                refine ⟨28188683961619996855443235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37584911948826662473924313 28188683961619996855443235)
                ·
                  refine ⟨42283025942429995283164853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28188683961619996855443235 42283025942429995283164853)
                  ·
                    refine ⟨3964033682102812057796705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42283025942429995283164853 3964033682102812057796705)
                    ·
                      refine ⟨2973025261577109043347529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964033682102812057796705 2973025261577109043347529)
                      ·
                        rfl

theorem cell23_5789946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_5789946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789946 prefixEnd_5789946 := by exact prefixLift 5789946
  have htrace : WordTrace (prefixWord ++ tailWord_5789946) baseStart_5789946 baseEnd_5789946 := by
    simpa [prefixWord, tailWord_5789946, baseEnd_5789946] using wordTrace_append hprefix tailTrace_5789946
  have hstable : (prefixWord ++ tailWord_5789946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789946).length < 2 ^ (prefixWord ++ tailWord_5789946).sum := by decide
  have hdescent : baseEnd_5789946 < baseStart_5789946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789976 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_5789976 : Nat := 118140960795 + 5789976 * 2 ^ 59
def prefixEnd_5789976 : Nat := 4983230072969 + 3 ^ 40 * 5789976 * 2
def baseEnd_5789976 : Nat := 2973040665996743925972391

theorem tailTrace_5789976 : CollatzResearch.WordTrace tailWord_5789976 prefixEnd_5789976 2973040665996743925972391 := by
  unfold tailWord_5789976
  simp only [CollatzResearch.WordTrace]
  refine ⟨105588886835956638009802891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140785182447942184013070521 105588886835956638009802891)
  ·
    refine ⟨158383330253934957014704337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105588886835956638009802891 158383330253934957014704337)
    ·
      refine ⟨118787497690451217761028253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158383330253934957014704337 118787497690451217761028253)
      ·
        refine ⟨44545311633919206660385595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118787497690451217761028253 44545311633919206660385595)
        ·
          refine ⟨66817967450878809990578393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44545311633919206660385595 66817967450878809990578393)
          ·
            refine ⟨50113475588159107492933795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66817967450878809990578393 50113475588159107492933795)
            ·
              refine ⟨75170213382238661239400693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50113475588159107492933795 75170213382238661239400693)
              ·
                refine ⟨7047207504584874491193815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75170213382238661239400693 7047207504584874491193815)
                ·
                  refine ⟨10570811256877311736790723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047207504584874491193815 10570811256877311736790723)
                  ·
                    refine ⟨15856216885315967605186085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10570811256877311736790723 15856216885315967605186085)
                    ·
                      refine ⟨2973040665996743925972391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15856216885315967605186085 2973040665996743925972391)
                      ·
                        rfl

theorem cell23_5789976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_5789976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789976 prefixEnd_5789976 := by exact prefixLift 5789976
  have htrace : WordTrace (prefixWord ++ tailWord_5789976) baseStart_5789976 baseEnd_5789976 := by
    simpa [prefixWord, tailWord_5789976, baseEnd_5789976] using wordTrace_append hprefix tailTrace_5789976
  have hstable : (prefixWord ++ tailWord_5789976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789976).length < 2 ^ (prefixWord ++ tailWord_5789976).sum := by decide
  have hdescent : baseEnd_5789976 < baseStart_5789976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789979 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5]
def baseStart_5789979 : Nat := 118140960795 + 5789979 * 2 ^ 59
def prefixEnd_5789979 : Nat := 4983230072969 + 3 ^ 40 * 5789979 * 2
def baseEnd_5789979 : Nat := 2973042206438707414234877

theorem tailTrace_5789979 : CollatzResearch.WordTrace tailWord_5789979 prefixEnd_5789979 2973042206438707414234877 := by
  unfold tailWord_5789979
  simp only [CollatzResearch.WordTrace]
  refine ⟨211177883090902407531964991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140785255393934938354643327 211177883090902407531964991)
  ·
    refine ⟨316766824636353611297947487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211177883090902407531964991 316766824636353611297947487)
    ·
      refine ⟨475150236954530416946921231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316766824636353611297947487 475150236954530416946921231)
      ·
        refine ⟨712725355431795625420381847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475150236954530416946921231 712725355431795625420381847)
        ·
          refine ⟨1069088033147693438130572771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712725355431795625420381847 1069088033147693438130572771)
          ·
            refine ⟨1603632049721540157195859157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069088033147693438130572771 1603632049721540157195859157)
            ·
              refine ⟨37585126165348597434277949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1603632049721540157195859157 37585126165348597434277949)
              ·
                refine ⟨14094422312005724037854231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37585126165348597434277949 14094422312005724037854231)
                ·
                  refine ⟨21141633468008586056781347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14094422312005724037854231 21141633468008586056781347)
                  ·
                    refine ⟨31712450202012879085172021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21141633468008586056781347 31712450202012879085172021)
                    ·
                      refine ⟨2973042206438707414234877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31712450202012879085172021 2973042206438707414234877)
                      ·
                        rfl

theorem cell23_5789979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_5789979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789979 prefixEnd_5789979 := by exact prefixLift 5789979
  have htrace : WordTrace (prefixWord ++ tailWord_5789979) baseStart_5789979 baseEnd_5789979 := by
    simpa [prefixWord, tailWord_5789979, baseEnd_5789979] using wordTrace_append hprefix tailTrace_5789979
  have hstable : (prefixWord ++ tailWord_5789979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789979).length < 2 ^ (prefixWord ++ tailWord_5789979).sum := by decide
  have hdescent : baseEnd_5789979 < baseStart_5789979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790053 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_5790053 : Nat := 118140960795 + 5790053 * 2 ^ 59
def prefixEnd_5790053 : Nat := 4983230072969 + 3 ^ 40 * 5790053 * 2
def baseEnd_5790053 : Nat := 2973080204007140124709537

theorem tailTrace_5790053 : CollatzResearch.WordTrace tailWord_5790053 prefixEnd_5790053 2973080204007140124709537 := by
  unfold tailWord_5790053
  simp only [CollatzResearch.WordTrace]
  refine ⟨211180582092634318170158813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140787054728422878780105875 211180582092634318170158813)
  ·
    refine ⟨79192718284737869313809555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211180582092634318170158813 79192718284737869313809555)
    ·
      refine ⟨118789077427106803970714333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79192718284737869313809555 118789077427106803970714333)
      ·
        refine ⟨44545904035165051489017875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118789077427106803970714333 44545904035165051489017875)
        ·
          refine ⟨66818856052747577233526813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44545904035165051489017875 66818856052747577233526813)
          ·
            refine ⟨25057071019780341462572555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66818856052747577233526813 25057071019780341462572555)
            ·
              refine ⟨37585606529670512193858833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25057071019780341462572555 37585606529670512193858833)
              ·
                refine ⟨28189204897252884145394125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37585606529670512193858833 28189204897252884145394125)
                ·
                  refine ⟨10570951836469831554522797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28189204897252884145394125 10570951836469831554522797)
                  ·
                    refine ⟨3964106938676186832946049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10570951836469831554522797 3964106938676186832946049)
                    ·
                      refine ⟨2973080204007140124709537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964106938676186832946049 2973080204007140124709537)
                      ·
                        rfl

theorem cell23_5790053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_5790053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790053 prefixEnd_5790053 := by exact prefixLift 5790053
  have htrace : WordTrace (prefixWord ++ tailWord_5790053) baseStart_5790053 baseEnd_5790053 := by
    simpa [prefixWord, tailWord_5790053, baseEnd_5790053] using wordTrace_append hprefix tailTrace_5790053
  have hstable : (prefixWord ++ tailWord_5790053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790053).length < 2 ^ (prefixWord ++ tailWord_5790053).sum := by decide
  have hdescent : baseEnd_5790053 < baseStart_5790053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790059 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 2, 6]
def baseStart_5790059 : Nat := 118140960795 + 5790059 * 2 ^ 59
def prefixEnd_5790059 : Nat := 4983230072969 + 3 ^ 40 * 5790059 * 2
def baseEnd_5790059 : Nat := 991027761630355700411503

theorem tailTrace_5790059 : CollatzResearch.WordTrace tailWord_5790059 prefixEnd_5790059 991027761630355700411503 := by
  unfold tailWord_5790059
  simp only [CollatzResearch.WordTrace]
  refine ⟨211180800930612581194877231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140787200620408387463251487 211180800930612581194877231)
  ·
    refine ⟨316771201395918871792315847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211180800930612581194877231 316771201395918871792315847)
    ·
      refine ⟨475156802093878307688473771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316771201395918871792315847 475156802093878307688473771)
      ·
        refine ⟨712735203140817461532710657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475156802093878307688473771 712735203140817461532710657)
        ·
          refine ⟨534551402355613096149532993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712735203140817461532710657 534551402355613096149532993)
          ·
            refine ⟨400913551766709822112149745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534551402355613096149532993 400913551766709822112149745)
            ·
              refine ⟨300685163825032366584112309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400913551766709822112149745 300685163825032366584112309)
              ·
                refine ⟨28189234108596784367260529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300685163825032366584112309 28189234108596784367260529)
                ·
                  refine ⟨21141925581447588275445397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28189234108596784367260529 21141925581447588275445397)
                  ·
                    refine ⟨991027761630355700411503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21141925581447588275445397 991027761630355700411503)
                    ·
                      rfl

theorem cell23_5790059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_5790059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790059 prefixEnd_5790059 := by exact prefixLift 5790059
  have htrace : WordTrace (prefixWord ++ tailWord_5790059) baseStart_5790059 baseEnd_5790059 := by
    simpa [prefixWord, tailWord_5790059, baseEnd_5790059] using wordTrace_append hprefix tailTrace_5790059
  have hstable : (prefixWord ++ tailWord_5790059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790059).length < 2 ^ (prefixWord ++ tailWord_5790059).sum := by decide
  have hdescent : baseEnd_5790059 < baseStart_5790059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790106 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_5790106 : Nat := 118140960795 + 5790106 * 2 ^ 59
def prefixEnd_5790106 : Nat := 4983230072969 + 3 ^ 40 * 5790106 * 2
def baseEnd_5790106 : Nat := 330345268720203157482977

theorem tailTrace_5790106 : CollatzResearch.WordTrace tailWord_5790106 prefixEnd_5790106 330345268720203157482977 := by
  unfold tailWord_5790106
  simp only [CollatzResearch.WordTrace]
  refine ⟨52795628790360577055459543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140788343440961538814558781 52795628790360577055459543)
  ·
    refine ⟨79193443185540865583189315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52795628790360577055459543 79193443185540865583189315)
    ·
      refine ⟨118790164778311298374783973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79193443185540865583189315 118790164778311298374783973)
      ·
        refine ⟨22273155895933368445271995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118790164778311298374783973 22273155895933368445271995)
        ·
          refine ⟨33409733843900052667907993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22273155895933368445271995 33409733843900052667907993)
          ·
            refine ⟨25057300382925039500930995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33409733843900052667907993 25057300382925039500930995)
            ·
              refine ⟨37585950574387559251396493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25057300382925039500930995 37585950574387559251396493)
              ·
                refine ⟨14094731465395334719273685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37585950574387559251396493 14094731465395334719273685)
                ·
                  refine ⟨330345268720203157482977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14094731465395334719273685 330345268720203157482977)
                  ·
                    rfl

theorem cell23_5790106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_5790106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790106 prefixEnd_5790106 := by exact prefixLift 5790106
  have htrace : WordTrace (prefixWord ++ tailWord_5790106) baseStart_5790106 baseEnd_5790106 := by
    simpa [prefixWord, tailWord_5790106, baseEnd_5790106] using wordTrace_append hprefix tailTrace_5790106
  have hstable : (prefixWord ++ tailWord_5790106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790106).length < 2 ^ (prefixWord ++ tailWord_5790106).sum := by decide
  have hdescent : baseEnd_5790106 < baseStart_5790106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790117 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_5790117 : Nat := 118140960795 + 5790117 * 2 ^ 59
def prefixEnd_5790117 : Nat := 4983230072969 + 3 ^ 40 * 5790117 * 2
def baseEnd_5790117 : Nat := 2973113066769027874309243

theorem tailTrace_5790117 : CollatzResearch.WordTrace tailWord_5790117 prefixEnd_5790117 2973113066769027874309243 := by
  unfold tailWord_5790117
  simp only [CollatzResearch.WordTrace]
  refine ⟨211182916364402457100488605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140788610909601638066992403 211182916364402457100488605)
  ·
    refine ⟨79193593636650921412683227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211182916364402457100488605 79193593636650921412683227)
    ·
      refine ⟨118790390454976382119024841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79193593636650921412683227 118790390454976382119024841)
      ·
        refine ⟨89092792841232286589268631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118790390454976382119024841 89092792841232286589268631)
        ·
          refine ⟨133639189261848429883902947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89092792841232286589268631 133639189261848429883902947)
          ·
            refine ⟨200458783892772644825854421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133639189261848429883902947 200458783892772644825854421)
            ·
              refine ⟨4698252747486858863105963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200458783892772644825854421 4698252747486858863105963)
              ·
                refine ⟨7047379121230288294658945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698252747486858863105963 7047379121230288294658945)
                ·
                  refine ⟨5285534340922716220994209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047379121230288294658945 5285534340922716220994209)
                  ·
                    refine ⟨3964150755692037165745657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285534340922716220994209 3964150755692037165745657)
                    ·
                      refine ⟨2973113066769027874309243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964150755692037165745657 2973113066769027874309243)
                      ·
                        rfl

theorem cell23_5790117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_5790117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790117 prefixEnd_5790117 := by exact prefixLift 5790117
  have htrace : WordTrace (prefixWord ++ tailWord_5790117) baseStart_5790117 baseEnd_5790117 := by
    simpa [prefixWord, tailWord_5790117, baseEnd_5790117] using wordTrace_append hprefix tailTrace_5790117
  have hstable : (prefixWord ++ tailWord_5790117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790117).length < 2 ^ (prefixWord ++ tailWord_5790117).sum := by decide
  have hdescent : baseEnd_5790117 < baseStart_5790117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790136 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_5790136 : Nat := 118140960795 + 5790136 * 2 ^ 59
def prefixEnd_5790136 : Nat := 4983230072969 + 3 ^ 40 * 5790136 * 2
def baseEnd_5790136 : Nat := 991040940967154433323885

theorem tailTrace_5790136 : CollatzResearch.WordTrace tailWord_5790136 prefixEnd_5790136 991040940967154433323885 := by
  unfold tailWord_5790136
  simp only [CollatzResearch.WordTrace]
  refine ⟨105591804675666811672715131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140789072900889082230286841 105591804675666811672715131)
  ·
    refine ⟨158387707013500217509072697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105591804675666811672715131 158387707013500217509072697)
    ·
      refine ⟨118790780260125163131804523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158387707013500217509072697 118790780260125163131804523)
      ·
        refine ⟨178186170390187744697706785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118790780260125163131804523 178186170390187744697706785)
        ·
          refine ⟨133639627792640808523280089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178186170390187744697706785 133639627792640808523280089)
          ·
            refine ⟨100229720844480606392460067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133639627792640808523280089 100229720844480606392460067)
            ·
              refine ⟨150344581266720909588690101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100229720844480606392460067 150344581266720909588690101)
              ·
                refine ⟨14094804493755085273939697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150344581266720909588690101 14094804493755085273939697)
                ·
                  refine ⟨10571103370316313955454773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14094804493755085273939697 10571103370316313955454773)
                  ·
                    refine ⟨991040940967154433323885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10571103370316313955454773 991040940967154433323885)
                    ·
                      rfl

theorem cell23_5790136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_5790136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790136 prefixEnd_5790136 := by exact prefixLift 5790136
  have htrace : WordTrace (prefixWord ++ tailWord_5790136) baseStart_5790136 baseEnd_5790136 := by
    simpa [prefixWord, tailWord_5790136, baseEnd_5790136] using wordTrace_append hprefix tailTrace_5790136
  have hstable : (prefixWord ++ tailWord_5790136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790136).length < 2 ^ (prefixWord ++ tailWord_5790136).sum := by decide
  have hdescent : baseEnd_5790136 < baseStart_5790136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790140 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 5]
def baseStart_5790140 : Nat := 118140960795 + 5790140 * 2 ^ 59
def prefixEnd_5790140 : Nat := 4983230072969 + 3 ^ 40 * 5790140 * 2
def baseEnd_5790140 : Nat := 330347208536009031591293

theorem tailTrace_5790140 : CollatzResearch.WordTrace tailWord_5790140 prefixEnd_5790140 330347208536009031591293 := by
  unfold tailWord_5790140
  simp only [CollatzResearch.WordTrace]
  refine ⟨105591877621659566014287937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140789170162212754685717249 105591877621659566014287937)
  ·
    refine ⟨79193908216244674510715953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105591877621659566014287937 79193908216244674510715953)
    ·
      refine ⟨59395431162183505883036965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79193908216244674510715953 59395431162183505883036965)
      ·
        refine ⟨11136643342909407353069431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59395431162183505883036965 11136643342909407353069431)
        ·
          refine ⟨16704965014364111029604147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11136643342909407353069431 16704965014364111029604147)
          ·
            refine ⟨25057447521546166544406221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16704965014364111029604147 25057447521546166544406221)
            ·
              refine ⟨9396542820579812454152333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25057447521546166544406221 9396542820579812454152333)
              ·
                refine ⟨3523703557717429670307125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9396542820579812454152333 3523703557717429670307125)
                ·
                  refine ⟨330347208536009031591293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523703557717429670307125 330347208536009031591293)
                  ·
                    rfl

theorem cell23_5790140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_5790140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790140 prefixEnd_5790140 := by exact prefixLift 5790140
  have htrace : WordTrace (prefixWord ++ tailWord_5790140) baseStart_5790140 baseEnd_5790140 := by
    simpa [prefixWord, tailWord_5790140, baseEnd_5790140] using wordTrace_append hprefix tailTrace_5790140
  have hstable : (prefixWord ++ tailWord_5790140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790140).length < 2 ^ (prefixWord ++ tailWord_5790140).sum := by decide
  have hdescent : baseEnd_5790140 < baseStart_5790140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790173 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5790173 : Nat := 118140960795 + 5790173 * 2 ^ 59
def prefixEnd_5790173 : Nat := 4983230072969 + 3 ^ 40 * 5790173 * 2
def baseEnd_5790173 : Nat := 2973141821685679655208985

theorem tailTrace_5790173 : CollatzResearch.WordTrace tailWord_5790173 prefixEnd_5790173 2973141821685679655208985 := by
  unfold tailWord_5790173
  simp only [CollatzResearch.WordTrace]
  refine ⟨211184958852199578664527173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140789972568133052443018115 211184958852199578664527173)
  ·
    refine ⟨39597179784787420999598845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211184958852199578664527173 39597179784787420999598845)
    ·
      refine ⟨14848942419295282874849567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39597179784787420999598845 14848942419295282874849567)
      ·
        refine ⟨22273413628942924312274351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14848942419295282874849567 22273413628942924312274351)
        ·
          refine ⟨33410120443414386468411527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22273413628942924312274351 33410120443414386468411527)
          ·
            refine ⟨50115180665121579702617291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33410120443414386468411527 50115180665121579702617291)
            ·
              refine ⟨75172770997682369553925937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50115180665121579702617291 75172770997682369553925937)
              ·
                refine ⟨56379578248261777165444453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75172770997682369553925937 56379578248261777165444453)
                ·
                  refine ⟨10571170921549083218520835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56379578248261777165444453 10571170921549083218520835)
                  ·
                    refine ⟨15856756382323624827781253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10571170921549083218520835 15856756382323624827781253)
                    ·
                      refine ⟨2973141821685679655208985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15856756382323624827781253 2973141821685679655208985)
                      ·
                        rfl

theorem cell23_5790173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5790173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790173 prefixEnd_5790173 := by exact prefixLift 5790173
  have htrace : WordTrace (prefixWord ++ tailWord_5790173) baseStart_5790173 baseEnd_5790173 := by
    simpa [prefixWord, tailWord_5790173, baseEnd_5790173] using wordTrace_append hprefix tailTrace_5790173
  have hstable : (prefixWord ++ tailWord_5790173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790173).length < 2 ^ (prefixWord ++ tailWord_5790173).sum := by decide
  have hdescent : baseEnd_5790173 < baseStart_5790173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790183 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 5, 4]
def baseStart_5790183 : Nat := 118140960795 + 5790183 * 2 ^ 59
def prefixEnd_5790183 : Nat := 4983230072969 + 3 ^ 40 * 5790183 * 2
def baseEnd_5790183 : Nat := 991048985497408205361313

theorem tailTrace_5790183 : CollatzResearch.WordTrace tailWord_5790183 prefixEnd_5790183 991048985497408205361313 := by
  unfold tailWord_5790183
  simp only [CollatzResearch.WordTrace]
  refine ⟨211185323582163350372391203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140790215721442233581594135 211185323582163350372391203)
  ·
    refine ⟨316777985373245025558586805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211185323582163350372391203 316777985373245025558586805)
    ·
      refine ⟨29697936128741721146117513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316777985373245025558586805 29697936128741721146117513)
      ·
        refine ⟨22273452096556290859588135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29697936128741721146117513 22273452096556290859588135)
        ·
          refine ⟨33410178144834436289382203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22273452096556290859588135 33410178144834436289382203)
          ·
            refine ⟨50115267217251654434073305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33410178144834436289382203 50115267217251654434073305)
            ·
              refine ⟨37586450412938740825554979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50115267217251654434073305 37586450412938740825554979)
              ·
                refine ⟨56379675619408111238332469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37586450412938740825554979 56379675619408111238332469)
                ·
                  refine ⟨5285594589319510428593669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56379675619408111238332469 5285594589319510428593669)
                  ·
                    refine ⟨991048985497408205361313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285594589319510428593669 991048985497408205361313)
                    ·
                      rfl

theorem cell23_5790183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_5790183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790183 prefixEnd_5790183 := by exact prefixLift 5790183
  have htrace : WordTrace (prefixWord ++ tailWord_5790183) baseStart_5790183 baseEnd_5790183 := by
    simpa [prefixWord, tailWord_5790183, baseEnd_5790183] using wordTrace_append hprefix tailTrace_5790183
  have hstable : (prefixWord ++ tailWord_5790183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790183).length < 2 ^ (prefixWord ++ tailWord_5790183).sum := by decide
  have hdescent : baseEnd_5790183 < baseStart_5790183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790190 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_5790190 : Nat := 118140960795 + 5790190 * 2 ^ 59
def prefixEnd_5790190 : Nat := 4983230072969 + 3 ^ 40 * 5790190 * 2
def baseEnd_5790190 : Nat := 2973150550856806088696407

theorem tailTrace_5790190 : CollatzResearch.WordTrace tailWord_5790190 prefixEnd_5790190 2973150550856806088696407 := by
  unfold tailWord_5790190
  simp only [CollatzResearch.WordTrace]
  refine ⟨26398197361642248820987003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140790385928758660378597349 26398197361642248820987003)
  ·
    refine ⟨39597296042463373231480505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26398197361642248820987003 39597296042463373231480505)
    ·
      refine ⟨29697972031847529923610379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39597296042463373231480505 29697972031847529923610379)
      ·
        refine ⟨44546958047771294885415569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29697972031847529923610379 44546958047771294885415569)
        ·
          refine ⟨33410218535828471164061677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44546958047771294885415569 33410218535828471164061677)
          ·
            refine ⟨12528831950935676686523129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33410218535828471164061677 12528831950935676686523129)
            ·
              refine ⟨9396623963201757514892347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12528831950935676686523129 9396623963201757514892347)
              ·
                refine ⟨14094935944802636272338521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396623963201757514892347 14094935944802636272338521)
                ·
                  refine ⟨10571201958601977204253891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14094935944802636272338521 10571201958601977204253891)
                  ·
                    refine ⟨15856802937902965806380837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10571201958601977204253891 15856802937902965806380837)
                    ·
                      refine ⟨2973150550856806088696407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15856802937902965806380837 2973150550856806088696407)
                      ·
                        rfl

theorem cell23_5790190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_5790190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790190 prefixEnd_5790190 := by exact prefixLift 5790190
  have htrace : WordTrace (prefixWord ++ tailWord_5790190) baseStart_5790190 baseEnd_5790190 := by
    simpa [prefixWord, tailWord_5790190, baseEnd_5790190] using wordTrace_append hprefix tailTrace_5790190
  have hstable : (prefixWord ++ tailWord_5790190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790190).length < 2 ^ (prefixWord ++ tailWord_5790190).sum := by decide
  have hdescent : baseEnd_5790190 < baseStart_5790190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790200 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 1, 4]
def baseStart_5790200 : Nat := 118140960795 + 5790200 * 2 ^ 59
def prefixEnd_5790200 : Nat := 4983230072969 + 3 ^ 40 * 5790200 * 2
def baseEnd_5790200 : Nat := 991051895221117016523787

theorem tailTrace_5790200 : CollatzResearch.WordTrace tailWord_5790200 prefixEnd_5790200 991051895221117016523787 := by
  unfold tailWord_5790200
  simp only [CollatzResearch.WordTrace]
  refine ⟨105592971811550881137880027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140790629082067841517173369 105592971811550881137880027)
  ·
    refine ⟨158389457717326321706820041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105592971811550881137880027 158389457717326321706820041)
    ·
      refine ⟨118792093287994741280115031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158389457717326321706820041 118792093287994741280115031)
      ·
        refine ⟨178188139931992111920172547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118792093287994741280115031 178188139931992111920172547)
        ·
          refine ⟨267282209897988167880258821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178188139931992111920172547 267282209897988167880258821)
          ·
            refine ⟨50115414355872781477548529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267282209897988167880258821 50115414355872781477548529)
            ·
              refine ⟨37586560766904586108161397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50115414355872781477548529 37586560766904586108161397)
              ·
                refine ⟨3523740071897304947640131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37586560766904586108161397 3523740071897304947640131)
                ·
                  refine ⟨5285610107845957421460197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523740071897304947640131 5285610107845957421460197)
                  ·
                    refine ⟨991051895221117016523787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5285610107845957421460197 991051895221117016523787)
                    ·
                      rfl

theorem cell23_5790200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_5790200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790200 prefixEnd_5790200 := by exact prefixLift 5790200
  have htrace : WordTrace (prefixWord ++ tailWord_5790200) baseStart_5790200 baseEnd_5790200 := by
    simpa [prefixWord, tailWord_5790200, baseEnd_5790200] using wordTrace_append hprefix tailTrace_5790200
  have hstable : (prefixWord ++ tailWord_5790200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790200).length < 2 ^ (prefixWord ++ tailWord_5790200).sum := by decide
  have hdescent : baseEnd_5790200 < baseStart_5790200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790216 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5790216 : Nat := 118140960795 + 5790216 * 2 ^ 59
def prefixEnd_5790216 : Nat := 4983230072969 + 3 ^ 40 * 5790216 * 2
def baseEnd_5790216 : Nat := 2973163901353822986971287

theorem tailTrace_5790216 : CollatzResearch.WordTrace tailWord_5790216 prefixEnd_5790216 2973163901353822986971287 := by
  unfold tailWord_5790216
  simp only [CollatzResearch.WordTrace]
  refine ⟨105593263595521898504171251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140791018127362531338895001 105593263595521898504171251)
  ·
    refine ⟨158389895393282847756256877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105593263595521898504171251 158389895393282847756256877)
    ·
      refine ⟨59396210772481067908596329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158389895393282847756256877 59396210772481067908596329)
      ·
        refine ⟨44547158079360800931447247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59396210772481067908596329 44547158079360800931447247)
        ·
          refine ⟨66820737119041201397170871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44547158079360800931447247 66820737119041201397170871)
          ·
            refine ⟨100231105678561802095756307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66820737119041201397170871 100231105678561802095756307)
            ·
              refine ⟨150346658517842703143634461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100231105678561802095756307 150346658517842703143634461)
              ·
                refine ⟨56379996944191013678862923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150346658517842703143634461 56379996944191013678862923)
                ·
                  refine ⟨84569995416286520518294385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56379996944191013678862923 84569995416286520518294385)
                  ·
                    refine ⟨63427496562214890388720789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84569995416286520518294385 63427496562214890388720789)
                    ·
                      refine ⟨2973163901353822986971287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63427496562214890388720789 2973163901353822986971287)
                      ·
                        rfl

theorem cell23_5790216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5790216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790216 prefixEnd_5790216 := by exact prefixLift 5790216
  have htrace : WordTrace (prefixWord ++ tailWord_5790216) baseStart_5790216 baseEnd_5790216 := by
    simpa [prefixWord, tailWord_5790216, baseEnd_5790216] using wordTrace_append hprefix tailTrace_5790216
  have hstable : (prefixWord ++ tailWord_5790216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790216).length < 2 ^ (prefixWord ++ tailWord_5790216).sum := by decide
  have hdescent : baseEnd_5790216 < baseStart_5790216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790233 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 5, 2]
def baseStart_5790233 : Nat := 118140960795 + 5790233 * 2 ^ 59
def prefixEnd_5790233 : Nat := 4983230072969 + 3 ^ 40 * 5790233 * 2
def baseEnd_5790233 : Nat := 2973172630524949420458709

theorem tailTrace_5790233 : CollatzResearch.WordTrace tailWord_5790233 prefixEnd_5790233 2973172630524949420458709 := by
  unfold tailWord_5790233
  simp only [CollatzResearch.WordTrace]
  refine ⟨211187147231982208911711353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140791431487988139274474235 211187147231982208911711353)
  ·
    refine ⟨158390360423986656683783515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211187147231982208911711353 158390360423986656683783515)
    ·
      refine ⟨237585540635979985025675273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158390360423986656683783515 237585540635979985025675273)
      ·
        refine ⟨178189155476984988769256455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237585540635979985025675273 178189155476984988769256455)
        ·
          refine ⟨267283733215477483153884683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178189155476984988769256455 267283733215477483153884683)
          ·
            refine ⟨400925599823216224730827025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267283733215477483153884683 400925599823216224730827025)
            ·
              refine ⟨300694199867412168548120269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400925599823216224730827025 300694199867412168548120269)
              ·
                refine ⟨112760324950279563205545101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300694199867412168548120269 112760324950279563205545101)
                ·
                  refine ⟨42285121856354836202079413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112760324950279563205545101 42285121856354836202079413)
                  ·
                    refine ⟨3964230174033265893944945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42285121856354836202079413 3964230174033265893944945)
                    ·
                      refine ⟨2973172630524949420458709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964230174033265893944945 2973172630524949420458709)
                      ·
                        rfl

theorem cell23_5790233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_5790233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790233 prefixEnd_5790233 := by exact prefixLift 5790233
  have htrace : WordTrace (prefixWord ++ tailWord_5790233) baseStart_5790233 baseEnd_5790233 := by
    simpa [prefixWord, tailWord_5790233, baseEnd_5790233] using wordTrace_append hprefix tailTrace_5790233
  have hstable : (prefixWord ++ tailWord_5790233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790233).length < 2 ^ (prefixWord ++ tailWord_5790233).sum := by decide
  have hdescent : baseEnd_5790233 < baseStart_5790233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790243 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 3, 5]
def baseStart_5790243 : Nat := 118140960795 + 5790243 * 2 ^ 59
def prefixEnd_5790243 : Nat := 4983230072969 + 3 ^ 40 * 5790243 * 2
def baseEnd_5790243 : Nat := 991059255110498127111221

theorem tailTrace_5790243 : CollatzResearch.WordTrace tailWord_5790243 prefixEnd_5790243 991059255110498127111221 := by
  unfold tailWord_5790243
  simp only [CollatzResearch.WordTrace]
  refine ⟨211187511961945980619575383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140791674641297320413050255 211187511961945980619575383)
  ·
    refine ⟨316781267942918970929363075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211187511961945980619575383 316781267942918970929363075)
    ·
      refine ⟨475171901914378456394044613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316781267942918970929363075 475171901914378456394044613)
      ·
        refine ⟨89094731608945960573883365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 475171901914378456394044613 89094731608945960573883365)
        ·
          refine ⟨16705262176677367607603131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89094731608945960573883365 16705262176677367607603131)
          ·
            refine ⟨25057893265016051411404697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16705262176677367607603131 25057893265016051411404697)
            ·
              refine ⟨18793419948762038558553523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25057893265016051411404697 18793419948762038558553523)
              ·
                refine ⟨28190129923143057837830285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18793419948762038558553523 28190129923143057837830285)
                ·
                  refine ⟨10571298721178646689186357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28190129923143057837830285 10571298721178646689186357)
                  ·
                    refine ⟨991059255110498127111221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10571298721178646689186357 991059255110498127111221)
                    ·
                      rfl

theorem cell23_5790243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 5].length) (baseStart_5790243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790243 prefixEnd_5790243 := by exact prefixLift 5790243
  have htrace : WordTrace (prefixWord ++ tailWord_5790243) baseStart_5790243 baseEnd_5790243 := by
    simpa [prefixWord, tailWord_5790243, baseEnd_5790243] using wordTrace_append hprefix tailTrace_5790243
  have hstable : (prefixWord ++ tailWord_5790243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790243).length < 2 ^ (prefixWord ++ tailWord_5790243).sum := by decide
  have hdescent : baseEnd_5790243 < baseStart_5790243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790244 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5790244 : Nat := 118140960795 + 5790244 * 2 ^ 59
def prefixEnd_5790244 : Nat := 4983230072969 + 3 ^ 40 * 5790244 * 2
def baseEnd_5790244 : Nat := 2973178278812148877421159

theorem tailTrace_5790244 : CollatzResearch.WordTrace tailWord_5790244 prefixEnd_5790244 2973178278812148877421159 := by
  unfold tailWord_5790244
  simp only [CollatzResearch.WordTrace]
  refine ⟨105593774217471178895180893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140791698956628238526907857 105593774217471178895180893)
  ·
    refine ⟨39597665331551692085692835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105593774217471178895180893 39597665331551692085692835)
    ·
      refine ⟨59396497997327538128539253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39597665331551692085692835 59396497997327538128539253)
      ·
        refine ⟨5568421687249456699550555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59396497997327538128539253 5568421687249456699550555)
        ·
          refine ⟨8352632530874185049325833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568421687249456699550555 8352632530874185049325833)
          ·
            refine ⟨6264474398155638786994375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8352632530874185049325833 6264474398155638786994375)
            ·
              refine ⟨9396711597233458180491563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264474398155638786994375 9396711597233458180491563)
              ·
                refine ⟨14095067395850187270737345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396711597233458180491563 14095067395850187270737345)
                ·
                  refine ⟨10571300546887640453053009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14095067395850187270737345 10571300546887640453053009)
                  ·
                    refine ⟨7928475410165730339789757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571300546887640453053009 7928475410165730339789757)
                    ·
                      refine ⟨2973178278812148877421159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928475410165730339789757 2973178278812148877421159)
                      ·
                        rfl

theorem cell23_5790244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5790244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790244 prefixEnd_5790244 := by exact prefixLift 5790244
  have htrace : WordTrace (prefixWord ++ tailWord_5790244) baseStart_5790244 baseEnd_5790244 := by
    simpa [prefixWord, tailWord_5790244, baseEnd_5790244] using wordTrace_append hprefix tailTrace_5790244
  have hstable : (prefixWord ++ tailWord_5790244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790244).length < 2 ^ (prefixWord ++ tailWord_5790244).sum := by decide
  have hdescent : baseEnd_5790244 < baseStart_5790244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790257 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 1, 1, 3]
def baseStart_5790257 : Nat := 118140960795 + 5790257 * 2 ^ 59
def prefixEnd_5790257 : Nat := 4983230072969 + 3 ^ 40 * 5790257 * 2
def baseEnd_5790257 : Nat := 2973184954060657326558599

theorem tailTrace_5790257 : CollatzResearch.WordTrace tailWord_5790257 prefixEnd_5790257 2973184954060657326558599 := by
  unfold tailWord_5790257
  simp only [CollatzResearch.WordTrace]
  refine ⟨211188022583895261010585025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140792015055930174007056683 211188022583895261010585025)
  ·
    refine ⟨158391016937921445757938769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211188022583895261010585025 158391016937921445757938769)
    ·
      refine ⟨118793262703441084318454077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158391016937921445757938769 118793262703441084318454077)
      ·
        refine ⟨44547473513790406619420279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118793262703441084318454077 44547473513790406619420279)
        ·
          refine ⟨66821210270685609929130419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44547473513790406619420279 66821210270685609929130419)
          ·
            refine ⟨100231815406028414893695629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66821210270685609929130419 100231815406028414893695629)
            ·
              refine ⟨37586930777260655585135861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100231815406028414893695629 37586930777260655585135861)
              ·
                refine ⟨3523774760368186461106487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37586930777260655585135861 3523774760368186461106487)
                ·
                  refine ⟨5285662140552279691659731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523774760368186461106487 5285662140552279691659731)
                  ·
                    refine ⟨7928493210828419537489597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5285662140552279691659731 7928493210828419537489597)
                    ·
                      refine ⟨2973184954060657326558599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928493210828419537489597 2973184954060657326558599)
                      ·
                        rfl

theorem cell23_5790257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_5790257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790257 prefixEnd_5790257 := by exact prefixLift 5790257
  have htrace : WordTrace (prefixWord ++ tailWord_5790257) baseStart_5790257 baseEnd_5790257 := by
    simpa [prefixWord, tailWord_5790257, baseEnd_5790257] using wordTrace_append hprefix tailTrace_5790257
  have hstable : (prefixWord ++ tailWord_5790257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790257).length < 2 ^ (prefixWord ++ tailWord_5790257).sum := by decide
  have hdescent : baseEnd_5790257 < baseStart_5790257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790283 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3]
def baseStart_5790283 : Nat := 118140960795 + 5790283 * 2 ^ 59
def prefixEnd_5790283 : Nat := 4983230072969 + 3 ^ 40 * 5790283 * 2
def baseEnd_5790283 : Nat := 2973198304557674224833479

theorem tailTrace_5790283 : CollatzResearch.WordTrace tailWord_5790283 prefixEnd_5790283 2973198304557674224833479 := by
  unfold tailWord_5790283
  simp only [CollatzResearch.WordTrace]
  refine ⟨211188970881801067451031503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140792647254534044967354335 211188970881801067451031503)
  ·
    refine ⟨316783456322701601176547255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211188970881801067451031503 316783456322701601176547255)
    ·
      refine ⟨475175184484052401764820883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316783456322701601176547255 475175184484052401764820883)
      ·
        refine ⟨712762776726078602647231325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475175184484052401764820883 712762776726078602647231325)
        ·
          refine ⟨267286041272279475992711747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 712762776726078602647231325 267286041272279475992711747)
          ·
            refine ⟨400929061908419213989067621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267286041272279475992711747 400929061908419213989067621)
            ·
              refine ⟨75174199107828602622950179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 400929061908419213989067621 75174199107828602622950179)
              ·
                refine ⟨112761298661742903934425269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75174199107828602622950179 112761298661742903934425269)
                ·
                  refine ⟨10571371749538397243852369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112761298661742903934425269 10571371749538397243852369)
                  ·
                    refine ⟨7928528812153797932889277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571371749538397243852369 7928528812153797932889277)
                    ·
                      refine ⟨2973198304557674224833479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928528812153797932889277 2973198304557674224833479)
                      ·
                        rfl

theorem cell23_5790283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3].length) (baseStart_5790283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790283 prefixEnd_5790283 := by exact prefixLift 5790283
  have htrace : WordTrace (prefixWord ++ tailWord_5790283) baseStart_5790283 baseEnd_5790283 := by
    simpa [prefixWord, tailWord_5790283, baseEnd_5790283] using wordTrace_append hprefix tailTrace_5790283
  have hstable : (prefixWord ++ tailWord_5790283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790283).length < 2 ^ (prefixWord ++ tailWord_5790283).sum := by decide
  have hdescent : baseEnd_5790283 < baseStart_5790283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790313 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_5790313 : Nat := 118140960795 + 5790313 * 2 ^ 59
def prefixEnd_5790313 : Nat := 4983230072969 + 3 ^ 40 * 5790313 * 2
def baseEnd_5790313 : Nat := 2973213708977309107458341

theorem tailTrace_5790313 : CollatzResearch.WordTrace tailWord_5790313 prefixEnd_5790313 2973213708977309107458341 := by
  unfold tailWord_5790313
  simp only [CollatzResearch.WordTrace]
  refine ⟨211190065071692382574623593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140793376714461588383082395 211190065071692382574623593)
  ·
    refine ⟨158392548803769286930967695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211190065071692382574623593 158392548803769286930967695)
    ·
      refine ⟨237588823205653930396451543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158392548803769286930967695 237588823205653930396451543)
      ·
        refine ⟨356383234808480895594677315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237588823205653930396451543 356383234808480895594677315)
        ·
          refine ⟨534574852212721343392015973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356383234808480895594677315 534574852212721343392015973)
          ·
            refine ⟨100232784789885251886002995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 534574852212721343392015973 100232784789885251886002995)
            ·
              refine ⟨150349177184827877829004493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100232784789885251886002995 150349177184827877829004493)
              ·
                refine ⟨56380941444310454185876685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150349177184827877829004493 56380941444310454185876685)
                ·
                  refine ⟨21142853041616420319703757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56380941444310454185876685 21142853041616420319703757)
                  ·
                    refine ⟨7928569890606157619888909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21142853041616420319703757 7928569890606157619888909)
                    ·
                      refine ⟨2973213708977309107458341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928569890606157619888909 2973213708977309107458341)
                      ·
                        rfl

theorem cell23_5790313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_5790313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790313 prefixEnd_5790313 := by exact prefixLift 5790313
  have htrace : WordTrace (prefixWord ++ tailWord_5790313) baseStart_5790313 baseEnd_5790313 := by
    simpa [prefixWord, tailWord_5790313, baseEnd_5790313] using wordTrace_append hprefix tailTrace_5790313
  have hstable : (prefixWord ++ tailWord_5790313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790313).length < 2 ^ (prefixWord ++ tailWord_5790313).sum := by decide
  have hdescent : baseEnd_5790313 < baseStart_5790313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790317 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_5790317 : Nat := 118140960795 + 5790317 * 2 ^ 59
def prefixEnd_5790317 : Nat := 4983230072969 + 3 ^ 40 * 5790317 * 2
def baseEnd_5790317 : Nat := 2973215762899927091808323

theorem tailTrace_5790317 : CollatzResearch.WordTrace tailWord_5790317 prefixEnd_5790317 2973215762899927091808323 := by
  unfold tailWord_5790317
  simp only [CollatzResearch.WordTrace]
  refine ⟨211190210963677891257769205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140793473975785260838512803 211190210963677891257769205)
  ·
    refine ⟨19799082277844802305415863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211190210963677891257769205 19799082277844802305415863)
    ·
      refine ⟨29698623416767203458123795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19799082277844802305415863 29698623416767203458123795)
      ·
        refine ⟨44547935125150805187185693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29698623416767203458123795 44547935125150805187185693)
        ·
          refine ⟨16705475671931551945194635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44547935125150805187185693 16705475671931551945194635)
          ·
            refine ⟨25058213507897327917791953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16705475671931551945194635 25058213507897327917791953)
            ·
              refine ⟨18793660130922995938343965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25058213507897327917791953 18793660130922995938343965)
              ·
                refine ⟨7047622549096123476878987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18793660130922995938343965 7047622549096123476878987)
                ·
                  refine ⟨10571433823644185215318481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047622549096123476878987 10571433823644185215318481)
                  ·
                    refine ⟨7928575367733138911488861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571433823644185215318481 7928575367733138911488861)
                    ·
                      refine ⟨2973215762899927091808323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928575367733138911488861 2973215762899927091808323)
                      ·
                        rfl

theorem cell23_5790317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_5790317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790317 prefixEnd_5790317 := by exact prefixLift 5790317
  have htrace : WordTrace (prefixWord ++ tailWord_5790317) baseStart_5790317 baseEnd_5790317 := by
    simpa [prefixWord, tailWord_5790317, baseEnd_5790317] using wordTrace_append hprefix tailTrace_5790317
  have hstable : (prefixWord ++ tailWord_5790317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790317).length < 2 ^ (prefixWord ++ tailWord_5790317).sum := by decide
  have hdescent : baseEnd_5790317 < baseStart_5790317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790320 : List Nat := [2, 1, 1, 1, 8, 1, 9]
def baseStart_5790320 : Nat := 118140960795 + 5790320 * 2 ^ 59
def prefixEnd_5790320 : Nat := 4983230072969 + 3 ^ 40 * 5790320 * 2
def baseEnd_5790320 : Nat := 36706386461010994815689

theorem tailTrace_5790320 : CollatzResearch.WordTrace tailWord_5790320 prefixEnd_5790320 36706386461010994815689 := by
  unfold tailWord_5790320
  simp only [CollatzResearch.WordTrace]
  refine ⟨105595160191333511385064207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140793546921778015180085609 105595160191333511385064207)
  ·
    refine ⟨158392740287000267077596311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105595160191333511385064207 158392740287000267077596311)
    ·
      refine ⟨237589110430500400616394467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158392740287000267077596311 237589110430500400616394467)
      ·
        refine ⟨356383665645750600924591701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237589110430500400616394467 356383665645750600924591701)
        ·
          refine ⟨4176371081786139854585059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 356383665645750600924591701 4176371081786139854585059)
          ·
            refine ⟨6264556622679209781877589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176371081786139854585059 6264556622679209781877589)
            ·
              refine ⟨36706386461010994815689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6264556622679209781877589 36706386461010994815689)
              ·
                rfl

theorem cell23_5790320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 9].length) (baseStart_5790320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790320 prefixEnd_5790320 := by exact prefixLift 5790320
  have htrace : WordTrace (prefixWord ++ tailWord_5790320) baseStart_5790320 baseEnd_5790320 := by
    simpa [prefixWord, tailWord_5790320, baseEnd_5790320] using wordTrace_append hprefix tailTrace_5790320
  have hstable : (prefixWord ++ tailWord_5790320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790320).length < 2 ^ (prefixWord ++ tailWord_5790320).sum := by decide
  have hdescent : baseEnd_5790320 < baseStart_5790320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790393 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 7]
def baseStart_5790393 : Nat := 118140960795 + 5790393 * 2 ^ 59
def prefixEnd_5790393 : Nat := 4983230072969 + 3 ^ 40 * 5790393 * 2
def baseEnd_5790393 : Nat := 330361643047740977161997

theorem tailTrace_5790393 : CollatzResearch.WordTrace tailWord_5790393 prefixEnd_5790393 330361643047740977161997 := by
  unfold tailWord_5790393
  simp only [CollatzResearch.WordTrace]
  refine ⟨211192982911402556237535833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140795321940935037491690555 211192982911402556237535833)
  ·
    refine ⟨158394737183551917178151875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211192982911402556237535833 158394737183551917178151875)
    ·
      refine ⟨237592105775327875767227813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158394737183551917178151875 237592105775327875767227813)
      ·
        refine ⟨44548519832873976706355215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237592105775327875767227813 44548519832873976706355215)
        ·
          refine ⟨66822779749310965059532823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44548519832873976706355215 66822779749310965059532823)
          ·
            refine ⟨100234169623966447589299235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66822779749310965059532823 100234169623966447589299235)
            ·
              refine ⟨150351254435949671383948853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100234169623966447589299235 150351254435949671383948853)
              ·
                refine ⟨14095430103370281692245205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150351254435949671383948853 14095430103370281692245205)
                ·
                  refine ⟨330361643047740977161997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14095430103370281692245205 330361643047740977161997)
                  ·
                    rfl

theorem cell23_5790393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_5790393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790393 prefixEnd_5790393 := by exact prefixLift 5790393
  have htrace : WordTrace (prefixWord ++ tailWord_5790393) baseStart_5790393 baseEnd_5790393 := by
    simpa [prefixWord, tailWord_5790393, baseEnd_5790393] using wordTrace_append hprefix tailTrace_5790393
  have hstable : (prefixWord ++ tailWord_5790393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790393).length < 2 ^ (prefixWord ++ tailWord_5790393).sum := by decide
  have hdescent : baseEnd_5790393 < baseStart_5790393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790400 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_5790400 : Nat := 118140960795 + 5790400 * 2 ^ 59
def prefixEnd_5790400 : Nat := 4983230072969 + 3 ^ 40 * 5790400 * 2
def baseEnd_5790400 : Nat := 2973258381794250267070441

theorem tailTrace_5790400 : CollatzResearch.WordTrace tailWord_5790400 prefixEnd_5790400 2973258381794250267070441 := by
  unfold tailWord_5790400
  simp only [CollatzResearch.WordTrace]
  refine ⟨105596619111188598216520327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140795492148251464288693769 105596619111188598216520327)
  ·
    refine ⟨158394928666782897324780491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105596619111188598216520327 158394928666782897324780491)
    ·
      refine ⟨237592393000174345987170737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158394928666782897324780491 237592393000174345987170737)
      ·
        refine ⟨178194294750130759490378053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237592393000174345987170737 178194294750130759490378053)
        ·
          refine ⟨33411430265649517404445885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178194294750130759490378053 33411430265649517404445885)
          ·
            refine ⟨12529286349618569026667207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33411430265649517404445885 12529286349618569026667207)
            ·
              refine ⟨18793929524427853540000811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529286349618569026667207 18793929524427853540000811)
              ·
                refine ⟨28190894286641780310001217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18793929524427853540000811 28190894286641780310001217)
                ·
                  refine ⟨21143170714981335232500913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28190894286641780310001217 21143170714981335232500913)
                  ·
                    refine ⟨15857378036236001424375685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21143170714981335232500913 15857378036236001424375685)
                    ·
                      refine ⟨2973258381794250267070441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15857378036236001424375685 2973258381794250267070441)
                      ·
                        rfl

theorem cell23_5790400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_5790400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790400 prefixEnd_5790400 := by exact prefixLift 5790400
  have htrace : WordTrace (prefixWord ++ tailWord_5790400) baseStart_5790400 baseEnd_5790400 := by
    simpa [prefixWord, tailWord_5790400, baseEnd_5790400] using wordTrace_append hprefix tailTrace_5790400
  have hstable : (prefixWord ++ tailWord_5790400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790400).length < 2 ^ (prefixWord ++ tailWord_5790400).sum := by decide
  have hdescent : baseEnd_5790400 < baseStart_5790400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790404 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5790404 : Nat := 118140960795 + 5790404 * 2 ^ 59
def prefixEnd_5790404 : Nat := 4983230072969 + 3 ^ 40 * 5790404 * 2
def baseEnd_5790404 : Nat := 2973260435716868251420423

theorem tailTrace_5790404 : CollatzResearch.WordTrace tailWord_5790404 prefixEnd_5790404 2973260435716868251420423 := by
  unfold tailWord_5790404
  simp only [CollatzResearch.WordTrace]
  refine ⟨105596692057181352558093133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140795589409575136744124177 105596692057181352558093133)
  ·
    refine ⟨39598759521443007209284925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105596692057181352558093133 39598759521443007209284925)
    ·
      refine ⟨14849534820541127703481847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39598759521443007209284925 14849534820541127703481847)
      ·
        refine ⟨22274302230811691555222771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14849534820541127703481847 22274302230811691555222771)
        ·
          refine ⟨33411453346217537332834157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22274302230811691555222771 33411453346217537332834157)
          ·
            refine ⟨12529295004831576499812809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33411453346217537332834157 12529295004831576499812809)
            ·
              refine ⟨9396971253623682374859607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12529295004831576499812809 9396971253623682374859607)
              ·
                refine ⟨14095456880435523562289411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396971253623682374859607 14095456880435523562289411)
                ·
                  refine ⟨21143185320653285343434117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14095456880435523562289411 21143185320653285343434117)
                  ·
                    refine ⟨3964347247622491001893897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21143185320653285343434117 3964347247622491001893897)
                    ·
                      refine ⟨2973260435716868251420423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964347247622491001893897 2973260435716868251420423)
                      ·
                        rfl

theorem cell23_5790404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5790404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790404 prefixEnd_5790404 := by exact prefixLift 5790404
  have htrace : WordTrace (prefixWord ++ tailWord_5790404) baseStart_5790404 baseEnd_5790404 := by
    simpa [prefixWord, tailWord_5790404, baseEnd_5790404] using wordTrace_append hprefix tailTrace_5790404
  have hstable : (prefixWord ++ tailWord_5790404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790404).length < 2 ^ (prefixWord ++ tailWord_5790404).sum := by decide
  have hdescent : baseEnd_5790404 < baseStart_5790404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790410 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_5790410 : Nat := 118140960795 + 5790410 * 2 ^ 59
def prefixEnd_5790410 : Nat := 4983230072969 + 3 ^ 40 * 5790410 * 2
def baseEnd_5790410 : Nat := 330362612955643914216155

theorem tailTrace_5790410 : CollatzResearch.WordTrace tailWord_5790410 prefixEnd_5790410 330362612955643914216155 := by
  unfold tailWord_5790410
  simp only [CollatzResearch.WordTrace]
  refine ⟨52798400738085242035226171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140795735301560645427269789 52798400738085242035226171)
  ·
    refine ⟨79197601107127863052839257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52798400738085242035226171 79197601107127863052839257)
    ·
      refine ⟨59398200830345897289629443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79197601107127863052839257 59398200830345897289629443)
      ·
        refine ⟨89097301245518845934444165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59398200830345897289629443 89097301245518845934444165)
        ·
          refine ⟨16705743983534783612708281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89097301245518845934444165 16705743983534783612708281)
          ·
            refine ⟨12529307987651087709531211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16705743983534783612708281 12529307987651087709531211)
            ·
              refine ⟨18793961981476631564296817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529307987651087709531211 18793961981476631564296817)
              ·
                refine ⟨14095471486107473673222613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18793961981476631564296817 14095471486107473673222613)
                ·
                  refine ⟨330362612955643914216155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14095471486107473673222613 330362612955643914216155)
                  ·
                    rfl

theorem cell23_5790410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_5790410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790410 prefixEnd_5790410 := by exact prefixLift 5790410
  have htrace : WordTrace (prefixWord ++ tailWord_5790410) baseStart_5790410 baseEnd_5790410 := by
    simpa [prefixWord, tailWord_5790410, baseEnd_5790410] using wordTrace_append hprefix tailTrace_5790410
  have hstable : (prefixWord ++ tailWord_5790410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790410).length < 2 ^ (prefixWord ++ tailWord_5790410).sum := by decide
  have hdescent : baseEnd_5790410 < baseStart_5790410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790460 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_5790460 : Nat := 118140960795 + 5790460 * 2 ^ 59
def prefixEnd_5790460 : Nat := 4983230072969 + 3 ^ 40 * 5790460 * 2
def baseEnd_5790460 : Nat := 2973289190633520032320165

theorem tailTrace_5790460 : CollatzResearch.WordTrace tailWord_5790460 prefixEnd_5790460 2973289190633520032320165 := by
  unfold tailWord_5790460
  simp only [CollatzResearch.WordTrace]
  refine ⟨105597713301079913340112417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140796951068106551120149889 105597713301079913340112417)
  ·
    refine ⟨79198284975809935005084313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105597713301079913340112417 79198284975809935005084313)
    ·
      refine ⟨59398713731857451253813235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79198284975809935005084313 59398713731857451253813235)
      ·
        refine ⟨89098070597786176880719853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59398713731857451253813235 89098070597786176880719853)
        ·
          refine ⟨33411776474169816330269945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89098070597786176880719853 33411776474169816330269945)
          ·
            refine ⟨25058832355627362247702459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33411776474169816330269945 25058832355627362247702459)
            ·
              refine ⟨37588248533441043371553689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25058832355627362247702459 37588248533441043371553689)
              ·
                refine ⟨28191186400080782528665267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37588248533441043371553689 28191186400080782528665267)
                ·
                  refine ⟨42286779600121173792997901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28191186400080782528665267 42286779600121173792997901)
                  ·
                    refine ⟨15857542350045440172374213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42286779600121173792997901 15857542350045440172374213)
                    ·
                      refine ⟨2973289190633520032320165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15857542350045440172374213 2973289190633520032320165)
                      ·
                        rfl

theorem cell23_5790460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_5790460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790460 prefixEnd_5790460 := by exact prefixLift 5790460
  have htrace : WordTrace (prefixWord ++ tailWord_5790460) baseStart_5790460 baseEnd_5790460 := by
    simpa [prefixWord, tailWord_5790460, baseEnd_5790460] using wordTrace_append hprefix tailTrace_5790460
  have hstable : (prefixWord ++ tailWord_5790460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790460).length < 2 ^ (prefixWord ++ tailWord_5790460).sum := by decide
  have hdescent : baseEnd_5790460 < baseStart_5790460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790483 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 10]
def baseStart_5790483 : Nat := 118140960795 + 5790483 * 2 ^ 59
def prefixEnd_5790483 : Nat := 4983230072969 + 3 ^ 40 * 5790483 * 2
def baseEnd_5790483 : Nat := 330366777854285938036951

theorem tailTrace_5790483 : CollatzResearch.WordTrace tailWord_5790483 prefixEnd_5790483 330366777854285938036951 := by
  unfold tailWord_5790483
  simp only [CollatzResearch.WordTrace]
  refine ⟨211196265481076501608312103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140797510320717667738874735 211196265481076501608312103)
  ·
    refine ⟨316794398221614752412468155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211196265481076501608312103 316794398221614752412468155)
    ·
      refine ⟨475191597332422128618702233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316794398221614752412468155 475191597332422128618702233)
      ·
        refine ⟨356393697999316596464026675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475191597332422128618702233 356393697999316596464026675)
        ·
          refine ⟨534590546998974894696040013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356393697999316596464026675 534590546998974894696040013)
          ·
            refine ⟨200471455124615585511015005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534590546998974894696040013 200471455124615585511015005)
            ·
              refine ⟨75176795671730844566630627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200471455124615585511015005 75176795671730844566630627)
              ·
                refine ⟨112765193507596266849945941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75176795671730844566630627 112765193507596266849945941)
                ·
                  refine ⟨330366777854285938036951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112765193507596266849945941 330366777854285938036951)
                  ·
                    rfl

theorem cell23_5790483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 10].length) (baseStart_5790483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790483 prefixEnd_5790483 := by exact prefixLift 5790483
  have htrace : WordTrace (prefixWord ++ tailWord_5790483) baseStart_5790483 baseEnd_5790483 := by
    simpa [prefixWord, tailWord_5790483, baseEnd_5790483] using wordTrace_append hprefix tailTrace_5790483
  have hstable : (prefixWord ++ tailWord_5790483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790483).length < 2 ^ (prefixWord ++ tailWord_5790483).sum := by decide
  have hdescent : baseEnd_5790483 < baseStart_5790483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790497 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5790497 : Nat := 118140960795 + 5790497 * 2 ^ 59
def prefixEnd_5790497 : Nat := 4983230072969 + 3 ^ 40 * 5790497 * 2
def baseEnd_5790497 : Nat := 2973308189417736387557495

theorem tailTrace_5790497 : CollatzResearch.WordTrace tailWord_5790497 prefixEnd_5790497 2973308189417736387557495 := by
  unfold tailWord_5790497
  simp only [CollatzResearch.WordTrace]
  refine ⟨211196776103025781999321745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140797850735350521332881163 211196776103025781999321745)
  ·
    refine ⟨158397582077269336499491309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211196776103025781999321745 158397582077269336499491309)
    ·
      refine ⟨59399093278976001187309241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158397582077269336499491309 59399093278976001187309241)
      ·
        refine ⟨44549319959232000890481931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59399093278976001187309241 44549319959232000890481931)
        ·
          refine ⟨66823979938848001335722897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44549319959232000890481931 66823979938848001335722897)
          ·
            refine ⟨50117984954136001001792173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66823979938848001335722897 50117984954136001001792173)
            ·
              refine ⟨18794244357801000375672065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50117984954136001001792173 18794244357801000375672065)
              ·
                refine ⟨14095683268350750281754049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18794244357801000375672065 14095683268350750281754049)
                ·
                  refine ⟨10571762451263062711315537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14095683268350750281754049 10571762451263062711315537)
                  ·
                    refine ⟨7928821838447297033486653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571762451263062711315537 7928821838447297033486653)
                    ·
                      refine ⟨2973308189417736387557495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928821838447297033486653 2973308189417736387557495)
                      ·
                        rfl

theorem cell23_5790497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5790497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790497 prefixEnd_5790497 := by exact prefixLift 5790497
  have htrace : WordTrace (prefixWord ++ tailWord_5790497) baseStart_5790497 baseEnd_5790497 := by
    simpa [prefixWord, tailWord_5790497, baseEnd_5790497] using wordTrace_append hprefix tailTrace_5790497
  have hstable : (prefixWord ++ tailWord_5790497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790497).length < 2 ^ (prefixWord ++ tailWord_5790497).sum := by decide
  have hdescent : baseEnd_5790497 < baseStart_5790497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790517 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 6]
def baseStart_5790517 : Nat := 118140960795 + 5790517 * 2 ^ 59
def prefixEnd_5790517 : Nat := 4983230072969 + 3 ^ 40 * 5790517 * 2
def baseEnd_5790517 : Nat := 330368717670091812145267

theorem tailTrace_5790517 : CollatzResearch.WordTrace tailWord_5790517 prefixEnd_5790517 330368717670091812145267 := by
  unfold tailWord_5790517
  simp only [CollatzResearch.WordTrace]
  refine ⟨211197505562953325415049805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140798337041968883610033203 211197505562953325415049805)
  ·
    refine ⟨79199064586107497030643677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211197505562953325415049805 79199064586107497030643677)
    ·
      refine ⟨29699649219790311386491379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79199064586107497030643677 29699649219790311386491379)
      ·
        refine ⟨44549473829685467079737069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29699649219790311386491379 44549473829685467079737069)
        ·
          refine ⟨16706052686132050154901401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44549473829685467079737069 16706052686132050154901401)
          ·
            refine ⟨12529539514599037616176051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16706052686132050154901401 12529539514599037616176051)
            ·
              refine ⟨18794309271898556424264077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529539514599037616176051 18794309271898556424264077)
              ·
                refine ⟨7047865976961958659099029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18794309271898556424264077 7047865976961958659099029)
                ·
                  refine ⟨330368717670091812145267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7047865976961958659099029 330368717670091812145267)
                  ·
                    rfl

theorem cell23_5790517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_5790517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790517 prefixEnd_5790517 := by exact prefixLift 5790517
  have htrace : WordTrace (prefixWord ++ tailWord_5790517) baseStart_5790517 baseEnd_5790517 := by
    simpa [prefixWord, tailWord_5790517, baseEnd_5790517] using wordTrace_append hprefix tailTrace_5790517
  have hstable : (prefixWord ++ tailWord_5790517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790517).length < 2 ^ (prefixWord ++ tailWord_5790517).sum := by decide
  have hdescent : baseEnd_5790517 < baseStart_5790517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790554 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_5790554 : Nat := 118140960795 + 5790554 * 2 ^ 59
def prefixEnd_5790554 : Nat := 4983230072969 + 3 ^ 40 * 5790554 * 2
def baseEnd_5790554 : Nat := 2973337457815042664544733

theorem tailTrace_5790554 : CollatzResearch.WordTrace tailWord_5790554 prefixEnd_5790554 2973337457815042664544733 := by
  unfold tailWord_5790554
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799713765954820183536679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140799236709212853822764477 52799713765954820183536679)
  ·
    refine ⟨79199570648932230275305019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52799713765954820183536679 79199570648932230275305019)
    ·
      refine ⟨118799355973398345412957529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79199570648932230275305019 118799355973398345412957529)
      ·
        refine ⟨89099516980048759059718147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118799355973398345412957529 89099516980048759059718147)
        ·
          refine ⟨133649275470073138589577221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89099516980048759059718147 133649275470073138589577221)
          ·
            refine ⟨25059239150638713485545729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133649275470073138589577221 25059239150638713485545729)
            ·
              refine ⟨18794429362979035114159297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25059239150638713485545729 18794429362979035114159297)
              ·
                refine ⟨14095822022234276335619473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18794429362979035114159297 14095822022234276335619473)
                ·
                  refine ⟨10571866516675707251714605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14095822022234276335619473 10571866516675707251714605)
                  ·
                    refine ⟨3964449943753390219392977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10571866516675707251714605 3964449943753390219392977)
                    ·
                      refine ⟨2973337457815042664544733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964449943753390219392977 2973337457815042664544733)
                      ·
                        rfl

theorem cell23_5790554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_5790554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790554 prefixEnd_5790554 := by exact prefixLift 5790554
  have htrace : WordTrace (prefixWord ++ tailWord_5790554) baseStart_5790554 baseEnd_5790554 := by
    simpa [prefixWord, tailWord_5790554, baseEnd_5790554] using wordTrace_append hprefix tailTrace_5790554
  have hstable : (prefixWord ++ tailWord_5790554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790554).length < 2 ^ (prefixWord ++ tailWord_5790554).sum := by decide
  have hdescent : baseEnd_5790554 < baseStart_5790554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790560 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_5790560 : Nat := 118140960795 + 5790560 * 2 ^ 59
def prefixEnd_5790560 : Nat := 4983230072969 + 3 ^ 40 * 5790560 * 2
def baseEnd_5790560 : Nat := 991113512899656547023235

theorem tailTrace_5790560 : CollatzResearch.WordTrace tailWord_5790560 prefixEnd_5790560 991113512899656547023235 := by
  unfold tailWord_5790560
  simp only [CollatzResearch.WordTrace]
  refine ⟨105599536950898771879432567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140799382601198362505910089 105599536950898771879432567)
  ·
    refine ⟨158399305426348157819148851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105599536950898771879432567 158399305426348157819148851)
    ·
      refine ⟨237598958139522236728723277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158399305426348157819148851 237598958139522236728723277)
      ·
        refine ⟨89099609302320838773271229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237598958139522236728723277 89099609302320838773271229)
        ·
          refine ⟨33412353488370314539976711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89099609302320838773271229 33412353488370314539976711)
          ·
            refine ⟨50118530232555471809965067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33412353488370314539976711 50118530232555471809965067)
            ·
              refine ⟨75177795348833207714947601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50118530232555471809965067 75177795348833207714947601)
              ·
                refine ⟨56383346511624905786210701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75177795348833207714947601 56383346511624905786210701)
                ·
                  refine ⟨21143754941859339669829013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56383346511624905786210701 21143754941859339669829013)
                  ·
                    refine ⟨991113512899656547023235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21143754941859339669829013 991113512899656547023235)
                    ·
                      rfl

theorem cell23_5790560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_5790560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790560 prefixEnd_5790560 := by exact prefixLift 5790560
  have htrace : WordTrace (prefixWord ++ tailWord_5790560) baseStart_5790560 baseEnd_5790560 := by
    simpa [prefixWord, tailWord_5790560, baseEnd_5790560] using wordTrace_append hprefix tailTrace_5790560
  have hstable : (prefixWord ++ tailWord_5790560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790560).length < 2 ^ (prefixWord ++ tailWord_5790560).sum := by decide
  have hdescent : baseEnd_5790560 < baseStart_5790560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790567 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_5790567 : Nat := 118140960795 + 5790567 * 2 ^ 59
def prefixEnd_5790567 : Nat := 4983230072969 + 3 ^ 40 * 5790567 * 2
def baseEnd_5790567 : Nat := 2973344133063551113682173

theorem tailTrace_5790567 : CollatzResearch.WordTrace tailWord_5790567 prefixEnd_5790567 2973344133063551113682173 := by
  unfold tailWord_5790567
  simp only [CollatzResearch.WordTrace]
  refine ⟨211199329212772183954369955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140799552808514789302913303 211199329212772183954369955)
  ·
    refine ⟨316798993819158275931554933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211199329212772183954369955 316798993819158275931554933)
    ·
      refine ⟨29699905670546088368583275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316798993819158275931554933 29699905670546088368583275)
      ·
        refine ⟨44549858505819132552874913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29699905670546088368583275 44549858505819132552874913)
        ·
          refine ⟨33412393879364349414656185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44549858505819132552874913 33412393879364349414656185)
          ·
            refine ⟨25059295409523262060992139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33412393879364349414656185 25059295409523262060992139)
            ·
              refine ⟨37588943114284893091488209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25059295409523262060992139 37588943114284893091488209)
              ·
                refine ⟨28191707335713669818616157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37588943114284893091488209 28191707335713669818616157)
                ·
                  refine ⟨10571890250892626181981059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28191707335713669818616157 10571890250892626181981059)
                  ·
                    refine ⟨15857835376338939272971589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10571890250892626181981059 15857835376338939272971589)
                    ·
                      refine ⟨2973344133063551113682173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15857835376338939272971589 2973344133063551113682173)
                      ·
                        rfl

theorem cell23_5790567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_5790567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790567 prefixEnd_5790567 := by exact prefixLift 5790567
  have htrace : WordTrace (prefixWord ++ tailWord_5790567) baseStart_5790567 baseEnd_5790567 := by
    simpa [prefixWord, tailWord_5790567, baseEnd_5790567] using wordTrace_append hprefix tailTrace_5790567
  have hstable : (prefixWord ++ tailWord_5790567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790567).length < 2 ^ (prefixWord ++ tailWord_5790567).sum := by decide
  have hdescent : baseEnd_5790567 < baseStart_5790567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790577 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_5790577 : Nat := 118140960795 + 5790577 * 2 ^ 59
def prefixEnd_5790577 : Nat := 4983230072969 + 3 ^ 40 * 5790577 * 2
def baseEnd_5790577 : Nat := 991116422623365358185709

theorem tailTrace_5790577 : CollatzResearch.WordTrace tailWord_5790577 prefixEnd_5790577 991116422623365358185709 := by
  unfold tailWord_5790577
  simp only [CollatzResearch.WordTrace]
  refine ⟨211199693942735955662233985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140799795961823970441489323 211199693942735955662233985)
  ·
    refine ⟨158399770457051966746675489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211199693942735955662233985 158399770457051966746675489)
    ·
      refine ⟨118799827842788975060006617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158399770457051966746675489 118799827842788975060006617)
      ·
        refine ⟨89099870882091731295004963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118799827842788975060006617 89099870882091731295004963)
        ·
          refine ⟨133649806323137596942507445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89099870882091731295004963 133649806323137596942507445)
          ·
            refine ⟨12529669342794149713360073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133649806323137596942507445 12529669342794149713360073)
            ·
              refine ⟨9397252007095612285020055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12529669342794149713360073 9397252007095612285020055)
              ·
                refine ⟨14095878010643418427530083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397252007095612285020055 14095878010643418427530083)
                ·
                  refine ⟨21143817015965127641295125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14095878010643418427530083 21143817015965127641295125)
                  ·
                    refine ⟨991116422623365358185709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21143817015965127641295125 991116422623365358185709)
                    ·
                      rfl

theorem cell23_5790577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_5790577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790577 prefixEnd_5790577 := by exact prefixLift 5790577
  have htrace : WordTrace (prefixWord ++ tailWord_5790577) baseStart_5790577 baseEnd_5790577 := by
    simpa [prefixWord, tailWord_5790577, baseEnd_5790577] using wordTrace_append hprefix tailTrace_5790577
  have hstable : (prefixWord ++ tailWord_5790577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790577).length < 2 ^ (prefixWord ++ tailWord_5790577).sum := by decide
  have hdescent : baseEnd_5790577 < baseStart_5790577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790587 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3]
def baseStart_5790587 : Nat := 118140960795 + 5790587 * 2 ^ 59
def prefixEnd_5790587 : Nat := 4983230072969 + 3 ^ 40 * 5790587 * 2
def baseEnd_5790587 : Nat := 2973354402676641035432081

theorem tailTrace_5790587 : CollatzResearch.WordTrace tailWord_5790587 prefixEnd_5790587 2973354402676641035432081 := by
  unfold tailWord_5790587
  simp only [CollatzResearch.WordTrace]
  refine ⟨211200058672699727370098015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140800039115133151580065343 211200058672699727370098015)
  ·
    refine ⟨316800088009049591055147023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211200058672699727370098015 316800088009049591055147023)
    ·
      refine ⟨475200132013574386582720535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316800088009049591055147023 475200132013574386582720535)
      ·
        refine ⟨712800198020361579874080803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475200132013574386582720535 712800198020361579874080803)
        ·
          refine ⟨1069200297030542369811121205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712800198020361579874080803 1069200297030542369811121205)
          ·
            refine ⟨100237527846613347169792613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1069200297030542369811121205 100237527846613347169792613)
            ·
              refine ⟨18794536471240002594336115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100237527846613347169792613 18794536471240002594336115)
              ·
                refine ⟨28191804706860003891504173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18794536471240002594336115 28191804706860003891504173)
                ·
                  refine ⟨10571926765072501459314065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28191804706860003891504173 10571926765072501459314065)
                  ·
                    refine ⟨7928945073804376094485549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571926765072501459314065 7928945073804376094485549)
                    ·
                      refine ⟨2973354402676641035432081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7928945073804376094485549 2973354402676641035432081)
                      ·
                        rfl

theorem cell23_5790587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3].length) (baseStart_5790587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790587 prefixEnd_5790587 := by exact prefixLift 5790587
  have htrace : WordTrace (prefixWord ++ tailWord_5790587) baseStart_5790587 baseEnd_5790587 := by
    simpa [prefixWord, tailWord_5790587, baseEnd_5790587] using wordTrace_append hprefix tailTrace_5790587
  have hstable : (prefixWord ++ tailWord_5790587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790587).length < 2 ^ (prefixWord ++ tailWord_5790587).sum := by decide
  have hdescent : baseEnd_5790587 < baseStart_5790587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790597 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_5790597 : Nat := 118140960795 + 5790597 * 2 ^ 59
def prefixEnd_5790597 : Nat := 4983230072969 + 3 ^ 40 * 5790597 * 2
def baseEnd_5790597 : Nat := 2973359537483185996307035

theorem tailTrace_5790597 : CollatzResearch.WordTrace tailWord_5790597 prefixEnd_5790597 2973359537483185996307035 := by
  unfold tailWord_5790597
  simp only [CollatzResearch.WordTrace]
  refine ⟨211200423402663499077962045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140800282268442332718641363 211200423402663499077962045)
  ·
    refine ⟨79200158775998812154235767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211200423402663499077962045 79200158775998812154235767)
    ·
      refine ⟨118800238163998218231353651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79200158775998812154235767 118800238163998218231353651)
      ·
        refine ⟨178200357245997327347030477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118800238163998218231353651 178200357245997327347030477)
        ·
          refine ⟨66825133967248997755136429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178200357245997327347030477 66825133967248997755136429)
          ·
            refine ⟨25059425237718374158176161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66825133967248997755136429 25059425237718374158176161)
            ·
              refine ⟨18794568928288780618632121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25059425237718374158176161 18794568928288780618632121)
              ·
                refine ⟨14095926696216585463974091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18794568928288780618632121 14095926696216585463974091)
                ·
                  refine ⟨21143890044324878195961137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14095926696216585463974091 21143890044324878195961137)
                  ·
                    refine ⟨15857917533243658646970853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21143890044324878195961137 15857917533243658646970853)
                    ·
                      refine ⟨2973359537483185996307035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15857917533243658646970853 2973359537483185996307035)
                      ·
                        rfl

theorem cell23_5790597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_5790597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790597 prefixEnd_5790597 := by exact prefixLift 5790597
  have htrace : WordTrace (prefixWord ++ tailWord_5790597) baseStart_5790597 baseEnd_5790597 := by
    simpa [prefixWord, tailWord_5790597, baseEnd_5790597] using wordTrace_append hprefix tailTrace_5790597
  have hstable : (prefixWord ++ tailWord_5790597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790597).length < 2 ^ (prefixWord ++ tailWord_5790597).sum := by decide
  have hdescent : baseEnd_5790597 < baseStart_5790597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790601 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 1, 1, 4]
def baseStart_5790601 : Nat := 118140960795 + 5790601 * 2 ^ 59
def prefixEnd_5790601 : Nat := 4983230072969 + 3 ^ 40 * 5790601 * 2
def baseEnd_5790601 : Nat := 2973361591405803980657017

theorem tailTrace_5790601 : CollatzResearch.WordTrace tailWord_5790601 prefixEnd_5790601 2973361591405803980657017 := by
  unfold tailWord_5790601
  simp only [CollatzResearch.WordTrace]
  refine ⟨211200569294649007761107657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140800379529766005174071771 211200569294649007761107657)
  ·
    refine ⟨158400426970986755820830743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211200569294649007761107657 158400426970986755820830743)
    ·
      refine ⟨237600640456480133731246115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158400426970986755820830743 237600640456480133731246115)
      ·
        refine ⟨356400960684720200596869173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237600640456480133731246115 356400960684720200596869173)
        ·
          refine ⟨33412590064192518805956485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 356400960684720200596869173 33412590064192518805956485)
          ·
            refine ⟨6264860637036097276116841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33412590064192518805956485 6264860637036097276116841)
            ·
              refine ⟨4698645477777072957087631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6264860637036097276116841 4698645477777072957087631)
              ·
                refine ⟨7047968216665609435631447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698645477777072957087631 7047968216665609435631447)
                ·
                  refine ⟨10571952324998414153447171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047968216665609435631447 10571952324998414153447171)
                  ·
                    refine ⟨15857928487497621230170757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10571952324998414153447171 15857928487497621230170757)
                    ·
                      refine ⟨2973361591405803980657017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15857928487497621230170757 2973361591405803980657017)
                      ·
                        rfl

theorem cell23_5790601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 1, 1, 4].length) (baseStart_5790601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790601 prefixEnd_5790601 := by exact prefixLift 5790601
  have htrace : WordTrace (prefixWord ++ tailWord_5790601) baseStart_5790601 baseEnd_5790601 := by
    simpa [prefixWord, tailWord_5790601, baseEnd_5790601] using wordTrace_append hprefix tailTrace_5790601
  have hstable : (prefixWord ++ tailWord_5790601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790601).length < 2 ^ (prefixWord ++ tailWord_5790601).sum := by decide
  have hdescent : baseEnd_5790601 < baseStart_5790601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790618 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5790618 : Nat := 118140960795 + 5790618 * 2 ^ 59
def prefixEnd_5790618 : Nat := 4983230072969 + 3 ^ 40 * 5790618 * 2
def baseEnd_5790618 : Nat := 2973370320576930414144439

theorem tailTrace_5790618 : CollatzResearch.WordTrace tailWord_5790618 prefixEnd_5790618 2973370320576930414144439 := by
  unfold tailWord_5790618
  simp only [CollatzResearch.WordTrace]
  refine ⟨52800297333896854916119127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140800792890391613109651005 52800297333896854916119127)
  ·
    refine ⟨79200446000845282374178691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52800297333896854916119127 79200446000845282374178691)
    ·
      refine ⟨118800669001267923561268037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79200446000845282374178691 118800669001267923561268037)
      ·
        refine ⟨22275125437737735667737757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118800669001267923561268037 22275125437737735667737757)
        ·
          refine ⟨8353172039151650875401659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22275125437737735667737757 8353172039151650875401659)
          ·
            refine ⟨12529758058727476313102489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353172039151650875401659 12529758058727476313102489)
            ·
              refine ⟨9397318544045607234826867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12529758058727476313102489 9397318544045607234826867)
              ·
                refine ⟨14095977816068410852240301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397318544045607234826867 14095977816068410852240301)
                ·
                  refine ⟨5285991681025654069590113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14095977816068410852240301 5285991681025654069590113)
                  ·
                    refine ⟨3964493760769240552192585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285991681025654069590113 3964493760769240552192585)
                    ·
                      refine ⟨2973370320576930414144439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964493760769240552192585 2973370320576930414144439)
                      ·
                        rfl

theorem cell23_5790618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5790618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790618 prefixEnd_5790618 := by exact prefixLift 5790618
  have htrace : WordTrace (prefixWord ++ tailWord_5790618) baseStart_5790618 baseEnd_5790618 := by
    simpa [prefixWord, tailWord_5790618, baseEnd_5790618] using wordTrace_append hprefix tailTrace_5790618
  have hstable : (prefixWord ++ tailWord_5790618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790618).length < 2 ^ (prefixWord ++ tailWord_5790618).sum := by decide
  have hdescent : baseEnd_5790618 < baseStart_5790618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790631 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5790631 : Nat := 118140960795 + 5790631 * 2 ^ 59
def prefixEnd_5790631 : Nat := 4983230072969 + 3 ^ 40 * 5790631 * 2
def baseEnd_5790631 : Nat := 2973376995825438863281879

theorem tailTrace_5790631 : CollatzResearch.WordTrace tailWord_5790631 prefixEnd_5790631 2973376995825438863281879 := by
  unfold tailWord_5790631
  simp only [CollatzResearch.WordTrace]
  refine ⟨211201663484540322884699747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140801108989693548589799831 211201663484540322884699747)
  ·
    refine ⟨316802495226810484327049621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211201663484540322884699747 316802495226810484327049621)
    ·
      refine ⟨14850116963756741452830451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 316802495226810484327049621 14850116963756741452830451)
      ·
        refine ⟨22275175445635112179245677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14850116963756741452830451 22275175445635112179245677)
        ·
          refine ⟨8353190792113167067217129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22275175445635112179245677 8353190792113167067217129)
          ·
            refine ⟨6264893094084875300412847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8353190792113167067217129 6264893094084875300412847)
            ·
              refine ⟨9397339641127312950619271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264893094084875300412847 9397339641127312950619271)
              ·
                refine ⟨14096009461690969425928907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397339641127312950619271 14096009461690969425928907)
                ·
                  refine ⟨21144014192536454138893361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14096009461690969425928907 21144014192536454138893361)
                  ·
                    refine ⟨15858010644402340604170021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21144014192536454138893361 15858010644402340604170021)
                    ·
                      refine ⟨2973376995825438863281879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15858010644402340604170021 2973376995825438863281879)
                      ·
                        rfl

theorem cell23_5790631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5790631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790631 prefixEnd_5790631 := by exact prefixLift 5790631
  have htrace : WordTrace (prefixWord ++ tailWord_5790631) baseStart_5790631 baseEnd_5790631 := by
    simpa [prefixWord, tailWord_5790631, baseEnd_5790631] using wordTrace_append hprefix tailTrace_5790631
  have hstable : (prefixWord ++ tailWord_5790631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790631).length < 2 ^ (prefixWord ++ tailWord_5790631).sum := by decide
  have hdescent : baseEnd_5790631 < baseStart_5790631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790641 : List Nat := [1, 2, 2, 4, 4, 1, 2, 7]
def baseStart_5790641 : Nat := 118140960795 + 5790641 * 2 ^ 59
def prefixEnd_5790641 : Nat := 4983230072969 + 3 ^ 40 * 5790641 * 2
def baseEnd_5790641 : Nat := 110125264097480882376179

theorem tailTrace_5790641 : CollatzResearch.WordTrace tailWord_5790641 prefixEnd_5790641 110125264097480882376179 := by
  unfold tailWord_5790641
  simp only [CollatzResearch.WordTrace]
  refine ⟨211202028214504094592563777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140801352143002729728375851 211202028214504094592563777)
  ·
    refine ⟨158401521160878070944422833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211202028214504094592563777 158401521160878070944422833)
    ·
      refine ⟨118801140870658553208317125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158401521160878070944422833 118801140870658553208317125)
      ·
        refine ⟨22275213913248478726559461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118801140870658553208317125 22275213913248478726559461)
        ·
          refine ⟨4176602608734089761229899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22275213913248478726559461 4176602608734089761229899)
          ·
            refine ⟨6264903913101134641844849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176602608734089761229899 6264903913101134641844849)
            ·
              refine ⟨4698677934825850981383637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6264903913101134641844849 4698677934825850981383637)
              ·
                refine ⟨110125264097480882376179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4698677934825850981383637 110125264097480882376179)
                ·
                  rfl

theorem cell23_5790641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 7].length) (baseStart_5790641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790641 prefixEnd_5790641 := by exact prefixLift 5790641
  have htrace : WordTrace (prefixWord ++ tailWord_5790641) baseStart_5790641 baseEnd_5790641 := by
    simpa [prefixWord, tailWord_5790641, baseEnd_5790641] using wordTrace_append hprefix tailTrace_5790641
  have hstable : (prefixWord ++ tailWord_5790641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790641).length < 2 ^ (prefixWord ++ tailWord_5790641).sum := by decide
  have hdescent : baseEnd_5790641 < baseStart_5790641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790646 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5790646 : Nat := 118140960795 + 5790646 * 2 ^ 59
def prefixEnd_5790646 : Nat := 4983230072969 + 3 ^ 40 * 5790646 * 2
def baseEnd_5790646 : Nat := 2973384698035256304594311

theorem tailTrace_5790646 : CollatzResearch.WordTrace tailWord_5790646 prefixEnd_5790646 2973384698035256304594311 := by
  unfold tailWord_5790646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200138161217873777905987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140801473719657320297663861 13200138161217873777905987)
  ·
    refine ⟨19800207241826810666858981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13200138161217873777905987 19800207241826810666858981)
    ·
      refine ⟨3712538857842527000036059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19800207241826810666858981 3712538857842527000036059)
      ·
        refine ⟨5568808286763790500054089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712538857842527000036059 5568808286763790500054089)
        ·
          refine ⟨4176606215072842875040567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5568808286763790500054089 4176606215072842875040567)
          ·
            refine ⟨6264909322609264312560851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176606215072842875040567 6264909322609264312560851)
            ·
              refine ⟨9397363983913896468841277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264909322609264312560851 9397363983913896468841277)
              ·
                refine ⟨3524011493967711175815479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9397363983913896468841277 3524011493967711175815479)
                ·
                  refine ⟨5286017240951566763723219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524011493967711175815479 5286017240951566763723219)
                  ·
                    refine ⟨7929025861427350145584829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286017240951566763723219 7929025861427350145584829)
                    ·
                      refine ⟨2973384698035256304594311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929025861427350145584829 2973384698035256304594311)
                      ·
                        rfl

theorem cell23_5790646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5790646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790646 prefixEnd_5790646 := by exact prefixLift 5790646
  have htrace : WordTrace (prefixWord ++ tailWord_5790646) baseStart_5790646 baseEnd_5790646 := by
    simpa [prefixWord, tailWord_5790646, baseEnd_5790646] using wordTrace_append hprefix tailTrace_5790646
  have hstable : (prefixWord ++ tailWord_5790646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790646).length < 2 ^ (prefixWord ++ tailWord_5790646).sum := by decide
  have hdescent : baseEnd_5790646 < baseStart_5790646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790669 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5790669 : Nat := 118140960795 + 5790669 * 2 ^ 59
def prefixEnd_5790669 : Nat := 4983230072969 + 3 ^ 40 * 5790669 * 2
def baseEnd_5790669 : Nat := 2973396508090309714606705

theorem tailTrace_5790669 : CollatzResearch.WordTrace tailWord_5790669 prefixEnd_5790669 2973396508090309714606705 := by
  unfold tailWord_5790669
  simp only [CollatzResearch.WordTrace]
  refine ⟨211203049458402655374583061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140802032972268436916388707 211203049458402655374583061)
  ·
    refine ⟨9900142943362624470683581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211203049458402655374583061 9900142943362624470683581)
    ·
      refine ⟨3712553603760984176506343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9900142943362624470683581 3712553603760984176506343)
      ·
        refine ⟨5568830405641476264759515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712553603760984176506343 5568830405641476264759515)
        ·
          refine ⟨8353245608462214397139273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568830405641476264759515 8353245608462214397139273)
          ·
            refine ⟨6264934206346660797854455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8353245608462214397139273 6264934206346660797854455)
            ·
              refine ⟨9397401309519991196781683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264934206346660797854455 9397401309519991196781683)
              ·
                refine ⟨14096101964279986795172525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397401309519991196781683 14096101964279986795172525)
                ·
                  refine ⟨5286038236604995048189697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14096101964279986795172525 5286038236604995048189697)
                  ·
                    refine ⟨3964528677453746286142273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286038236604995048189697 3964528677453746286142273)
                    ·
                      refine ⟨2973396508090309714606705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964528677453746286142273 2973396508090309714606705)
                      ·
                        rfl

theorem cell23_5790669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5790669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790669 prefixEnd_5790669 := by exact prefixLift 5790669
  have htrace : WordTrace (prefixWord ++ tailWord_5790669) baseStart_5790669 baseEnd_5790669 := by
    simpa [prefixWord, tailWord_5790669, baseEnd_5790669] using wordTrace_append hprefix tailTrace_5790669
  have hstable : (prefixWord ++ tailWord_5790669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790669).length < 2 ^ (prefixWord ++ tailWord_5790669).sum := by decide
  have hdescent : baseEnd_5790669 < baseStart_5790669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790685 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5790685 : Nat := 118140960795 + 5790685 * 2 ^ 59
def prefixEnd_5790685 : Nat := 4983230072969 + 3 ^ 40 * 5790685 * 2
def baseEnd_5790685 : Nat := 2973404723780781652006631

theorem tailTrace_5790685 : CollatzResearch.WordTrace tailWord_5790685 prefixEnd_5790685 2973404723780781652006631 := by
  unfold tailWord_5790685
  simp only [CollatzResearch.WordTrace]
  refine ⟨211203633026344690107165509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140802422017563126738110339 211203633026344690107165509)
  ·
    refine ⟨39600681192439629395093533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211203633026344690107165509 39600681192439629395093533)
    ·
      refine ⟨14850255447164861023160075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39600681192439629395093533 14850255447164861023160075)
      ·
        refine ⟨22275383170747291534740113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14850255447164861023160075 22275383170747291534740113)
        ·
          refine ⟨16706537378060468651055085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22275383170747291534740113 16706537378060468651055085)
          ·
            refine ⟨6264951516772675744145657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16706537378060468651055085 6264951516772675744145657)
            ·
              refine ⟨4698713637579506808109243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6264951516772675744145657 4698713637579506808109243)
              ·
                refine ⟨7048070456369260212163865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698713637579506808109243 7048070456369260212163865)
                ·
                  refine ⟨5286052842276945159122899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048070456369260212163865 5286052842276945159122899)
                  ·
                    refine ⟨7929079263415417738684349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286052842276945159122899 7929079263415417738684349)
                    ·
                      refine ⟨2973404723780781652006631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929079263415417738684349 2973404723780781652006631)
                      ·
                        rfl

theorem cell23_5790685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5790685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790685 prefixEnd_5790685 := by exact prefixLift 5790685
  have htrace : WordTrace (prefixWord ++ tailWord_5790685) baseStart_5790685 baseEnd_5790685 := by
    simpa [prefixWord, tailWord_5790685, baseEnd_5790685] using wordTrace_append hprefix tailTrace_5790685
  have hstable : (prefixWord ++ tailWord_5790685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790685).length < 2 ^ (prefixWord ++ tailWord_5790685).sum := by decide
  have hdescent : baseEnd_5790685 < baseStart_5790685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790707 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3]
def baseStart_5790707 : Nat := 118140960795 + 5790707 * 2 ^ 59
def prefixEnd_5790707 : Nat := 4983230072969 + 3 ^ 40 * 5790707 * 2
def baseEnd_5790707 : Nat := 2973416020355180565931529

theorem tailTrace_5790707 : CollatzResearch.WordTrace tailWord_5790707 prefixEnd_5790707 2973416020355180565931529 := by
  unfold tailWord_5790707
  simp only [CollatzResearch.WordTrace]
  refine ⟨211204435432264987864466375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140802956954843325242977583 211204435432264987864466375)
  ·
    refine ⟨316806653148397481796699563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211204435432264987864466375 316806653148397481796699563)
    ·
      refine ⟨475209979722596222695049345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316806653148397481796699563 475209979722596222695049345)
      ·
        refine ⟨356407484791947167021287009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475209979722596222695049345 356407484791947167021287009)
        ·
          refine ⟨267305613593960375265965257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356407484791947167021287009 267305613593960375265965257)
          ·
            refine ⟨200479210195470281449473943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267305613593960375265965257 200479210195470281449473943)
            ·
              refine ⟨300718815293205422174210915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200479210195470281449473943 300718815293205422174210915)
              ·
                refine ⟨451078222939808133261316373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300718815293205422174210915 451078222939808133261316373)
                ·
                  refine ⟨21144291700303506246624205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 451078222939808133261316373 21144291700303506246624205)
                  ·
                    refine ⟨7929109387613814842484077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21144291700303506246624205 7929109387613814842484077)
                    ·
                      refine ⟨2973416020355180565931529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929109387613814842484077 2973416020355180565931529)
                      ·
                        rfl

theorem cell23_5790707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_5790707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790707 prefixEnd_5790707 := by exact prefixLift 5790707
  have htrace : WordTrace (prefixWord ++ tailWord_5790707) baseStart_5790707 baseEnd_5790707 := by
    simpa [prefixWord, tailWord_5790707, baseEnd_5790707] using wordTrace_append hprefix tailTrace_5790707
  have hstable : (prefixWord ++ tailWord_5790707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790707).length < 2 ^ (prefixWord ++ tailWord_5790707).sum := by decide
  have hdescent : baseEnd_5790707 < baseStart_5790707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790731 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 5]
def baseStart_5790731 : Nat := 118140960795 + 5790731 * 2 ^ 59
def prefixEnd_5790731 : Nat := 4983230072969 + 3 ^ 40 * 5790731 * 2
def baseEnd_5790731 : Nat := 330380927098987608003491

theorem tailTrace_5790731 : CollatzResearch.WordTrace tailWord_5790731 prefixEnd_5790731 330380927098987608003491 := by
  unfold tailWord_5790731
  simp only [CollatzResearch.WordTrace]
  refine ⟨211205310784178039963340047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140803540522785359975560031 211205310784178039963340047)
  ·
    refine ⟨316807966176267059945010071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211205310784178039963340047 316807966176267059945010071)
    ·
      refine ⟨475211949264400589917515107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316807966176267059945010071 475211949264400589917515107)
      ·
        refine ⟨712817923896600884876272661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475211949264400589917515107 712817923896600884876272661)
        ·
          refine ⟨33413340182653166478575281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 712817923896600884876272661 33413340182653166478575281)
          ·
            refine ⟨25060005136989874858931461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33413340182653166478575281 25060005136989874858931461)
            ·
              refine ⟨4698750963185601536049649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25060005136989874858931461 4698750963185601536049649)
              ·
                refine ⟨3524063222389201152037237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698750963185601536049649 3524063222389201152037237)
                ·
                  refine ⟨330380927098987608003491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524063222389201152037237 330380927098987608003491)
                  ·
                    rfl

theorem cell23_5790731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 5].length) (baseStart_5790731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790731 prefixEnd_5790731 := by exact prefixLift 5790731
  have htrace : WordTrace (prefixWord ++ tailWord_5790731) baseStart_5790731 baseEnd_5790731 := by
    simpa [prefixWord, tailWord_5790731, baseEnd_5790731] using wordTrace_append hprefix tailTrace_5790731
  have hstable : (prefixWord ++ tailWord_5790731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790731).length < 2 ^ (prefixWord ++ tailWord_5790731).sum := by decide
  have hdescent : baseEnd_5790731 < baseStart_5790731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790764 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_5790764 : Nat := 118140960795 + 5790764 * 2 ^ 59
def prefixEnd_5790764 : Nat := 4983230072969 + 3 ^ 40 * 5790764 * 2
def baseEnd_5790764 : Nat := 2973445288752486842918767

theorem tailTrace_5790764 : CollatzResearch.WordTrace tailWord_5790764 prefixEnd_5790764 2973445288752486842918767 := by
  unfold tailWord_5790764
  simp only [CollatzResearch.WordTrace]
  refine ⟨105603257196529243299645673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140804342928705657732860897 105603257196529243299645673)
  ·
    refine ⟨79202442897396932474734255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105603257196529243299645673 79202442897396932474734255)
    ·
      refine ⟨118803664346095398712101383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79202442897396932474734255 118803664346095398712101383)
      ·
        refine ⟨178205496519143098068152075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118803664346095398712101383 178205496519143098068152075)
        ·
          refine ⟨267308244778714647102228113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178205496519143098068152075 267308244778714647102228113)
          ·
            refine ⟨200481183584035985326671085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267308244778714647102228113 200481183584035985326671085)
            ·
              refine ⟨75180443844013494497501657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200481183584035985326671085 75180443844013494497501657)
              ·
                refine ⟨56385332883010120873126243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75180443844013494497501657 56385332883010120873126243)
                ·
                  refine ⟨84577999324515181309689365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56385332883010120873126243 84577999324515181309689365)
                  ·
                    refine ⟨3964593718336649123891689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84577999324515181309689365 3964593718336649123891689)
                    ·
                      refine ⟨2973445288752486842918767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964593718336649123891689 2973445288752486842918767)
                      ·
                        rfl

theorem cell23_5790764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_5790764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790764 prefixEnd_5790764 := by exact prefixLift 5790764
  have htrace : WordTrace (prefixWord ++ tailWord_5790764) baseStart_5790764 baseEnd_5790764 := by
    simpa [prefixWord, tailWord_5790764, baseEnd_5790764] using wordTrace_append hprefix tailTrace_5790764
  have hstable : (prefixWord ++ tailWord_5790764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790764).length < 2 ^ (prefixWord ++ tailWord_5790764).sum := by decide
  have hdescent : baseEnd_5790764 < baseStart_5790764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790781 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5790781 : Nat := 118140960795 + 5790781 * 2 ^ 59
def prefixEnd_5790781 : Nat := 4983230072969 + 3 ^ 40 * 5790781 * 2
def baseEnd_5790781 : Nat := 2973454017923613276406189

theorem tailTrace_5790781 : CollatzResearch.WordTrace tailWord_5790781 prefixEnd_5790781 2973454017923613276406189 := by
  unfold tailWord_5790781
  simp only [CollatzResearch.WordTrace]
  refine ⟨211207134433996898502660197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140804756289331265668440131 211207134433996898502660197)
  ·
    refine ⟨39601337706374418469248787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211207134433996898502660197 39601337706374418469248787)
    ·
      refine ⟨59402006559561627703873181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39601337706374418469248787 59402006559561627703873181)
      ·
        refine ⟨22275752459835610388952443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59402006559561627703873181 22275752459835610388952443)
        ·
          refine ⟨33413628689753415583428665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22275752459835610388952443 33413628689753415583428665)
          ·
            refine ⟨25060221517315061687571499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33413628689753415583428665 25060221517315061687571499)
            ·
              refine ⟨37590332275972592531357249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25060221517315061687571499 37590332275972592531357249)
              ·
                refine ⟨28192749206979444398517937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37590332275972592531357249 28192749206979444398517937)
                ·
                  refine ⟨21144561905234583298888453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28192749206979444398517937 21144561905234583298888453)
                  ·
                    refine ⟨3964605357231484368541585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21144561905234583298888453 3964605357231484368541585)
                    ·
                      refine ⟨2973454017923613276406189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964605357231484368541585 2973454017923613276406189)
                      ·
                        rfl

theorem cell23_5790781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5790781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790781 prefixEnd_5790781 := by exact prefixLift 5790781
  have htrace : WordTrace (prefixWord ++ tailWord_5790781) baseStart_5790781 baseEnd_5790781 := by
    simpa [prefixWord, tailWord_5790781, baseEnd_5790781] using wordTrace_append hprefix tailTrace_5790781
  have hstable : (prefixWord ++ tailWord_5790781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790781).length < 2 ^ (prefixWord ++ tailWord_5790781).sum := by decide
  have hdescent : baseEnd_5790781 < baseStart_5790781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790784 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_5790784 : Nat := 118140960795 + 5790784 * 2 ^ 59
def prefixEnd_5790784 : Nat := 4983230072969 + 3 ^ 40 * 5790784 * 2
def baseEnd_5790784 : Nat := 2973455558365576764668675

theorem tailTrace_5790784 : CollatzResearch.WordTrace tailWord_5790784 prefixEnd_5790784 2973455558365576764668675 := by
  unfold tailWord_5790784
  simp only [CollatzResearch.WordTrace]
  refine ⟨105603621926493015007509703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140804829235324020010012937 105603621926493015007509703)
  ·
    refine ⟨158405432889739522511264555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105603621926493015007509703 158405432889739522511264555)
    ·
      refine ⟨237608149334609283766896833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158405432889739522511264555 237608149334609283766896833)
      ·
        refine ⟨178206112000956962825172625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237608149334609283766896833 178206112000956962825172625)
        ·
          refine ⟨133654584000717722118879469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178206112000956962825172625 133654584000717722118879469)
          ·
            refine ⟨50120469000269145794579801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133654584000717722118879469 50120469000269145794579801)
            ·
              refine ⟨37590351750201859345934851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50120469000269145794579801 37590351750201859345934851)
              ·
                refine ⟨56385527625302789018902277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37590351750201859345934851 56385527625302789018902277)
                ·
                  refine ⟨10572286429744272941044177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56385527625302789018902277 10572286429744272941044177)
                  ·
                    refine ⟨7929214822308204705783133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10572286429744272941044177 7929214822308204705783133)
                    ·
                      refine ⟨2973455558365576764668675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929214822308204705783133 2973455558365576764668675)
                      ·
                        rfl

theorem cell23_5790784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_5790784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790784 prefixEnd_5790784 := by exact prefixLift 5790784
  have htrace : WordTrace (prefixWord ++ tailWord_5790784) baseStart_5790784 baseEnd_5790784 := by
    simpa [prefixWord, tailWord_5790784, baseEnd_5790784] using wordTrace_append hprefix tailTrace_5790784
  have hstable : (prefixWord ++ tailWord_5790784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790784).length < 2 ^ (prefixWord ++ tailWord_5790784).sum := by decide
  have hdescent : baseEnd_5790784 < baseStart_5790784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790787 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 8]
def baseStart_5790787 : Nat := 118140960795 + 5790787 * 2 ^ 59
def prefixEnd_5790787 : Nat := 4983230072969 + 3 ^ 40 * 5790787 * 2
def baseEnd_5790787 : Nat := 330384122089726694770129

theorem tailTrace_5790787 : CollatzResearch.WordTrace tailWord_5790787 prefixEnd_5790787 330384122089726694770129 := by
  unfold tailWord_5790787
  simp only [CollatzResearch.WordTrace]
  refine ⟨211207353271975161527378615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140804902181316774351585743 211207353271975161527378615)
  ·
    refine ⟨316811029907962742291067923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211207353271975161527378615 316811029907962742291067923)
    ·
      refine ⟨475216544861944113436601885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316811029907962742291067923 475216544861944113436601885)
      ·
        refine ⟨178206204323229042538725707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475216544861944113436601885 178206204323229042538725707)
        ·
          refine ⟨267309306484843563808088561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178206204323229042538725707 267309306484843563808088561)
          ·
            refine ⟨200481979863632672856066421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267309306484843563808088561 200481979863632672856066421)
            ·
              refine ⟨18795185612215563080256227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200481979863632672856066421 18795185612215563080256227)
              ·
                refine ⟨28192778418323344620384341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18795185612215563080256227 28192778418323344620384341)
                ·
                  refine ⟨330384122089726694770129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28192778418323344620384341 330384122089726694770129)
                  ·
                    rfl

theorem cell23_5790787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 8].length) (baseStart_5790787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790787 prefixEnd_5790787 := by exact prefixLift 5790787
  have htrace : WordTrace (prefixWord ++ tailWord_5790787) baseStart_5790787 baseEnd_5790787 := by
    simpa [prefixWord, tailWord_5790787, baseEnd_5790787] using wordTrace_append hprefix tailTrace_5790787
  have hstable : (prefixWord ++ tailWord_5790787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790787).length < 2 ^ (prefixWord ++ tailWord_5790787).sum := by decide
  have hdescent : baseEnd_5790787 < baseStart_5790787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790791 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 3, 4]
def baseStart_5790791 : Nat := 118140960795 + 5790791 * 2 ^ 59
def prefixEnd_5790791 : Nat := 4983230072969 + 3 ^ 40 * 5790791 * 2
def baseEnd_5790791 : Nat := 991153050910052745760381

theorem tailTrace_5790791 : CollatzResearch.WordTrace tailWord_5790791 prefixEnd_5790791 991153050910052745760381 := by
  unfold tailWord_5790791
  simp only [CollatzResearch.WordTrace]
  refine ⟨211207499163960670210524227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140804999442640446807016151 211207499163960670210524227)
  ·
    refine ⟨316811248745941005315786341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211207499163960670210524227 316811248745941005315786341)
    ·
      refine ⟨59402109139863938496709939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316811248745941005315786341 59402109139863938496709939)
      ·
        refine ⟨89103163709795907745064909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59402109139863938496709939 89103163709795907745064909)
        ·
          refine ⟨33413686391173465404399341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89103163709795907745064909 33413686391173465404399341)
          ·
            refine ⟨12530132396690049526649753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33413686391173465404399341 12530132396690049526649753)
            ·
              refine ⟨9397599297517537144987315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12530132396690049526649753 9397599297517537144987315)
              ·
                refine ⟨14096398946276305717480973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397599297517537144987315 14096398946276305717480973)
                ·
                  refine ⟨5286149604853614644055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14096398946276305717480973 5286149604853614644055365)
                  ·
                    refine ⟨991153050910052745760381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286149604853614644055365 991153050910052745760381)
                    ·
                      rfl

theorem cell23_5790791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_5790791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790791 prefixEnd_5790791 := by exact prefixLift 5790791
  have htrace : WordTrace (prefixWord ++ tailWord_5790791) baseStart_5790791 baseEnd_5790791 := by
    simpa [prefixWord, tailWord_5790791, baseEnd_5790791] using wordTrace_append hprefix tailTrace_5790791
  have hstable : (prefixWord ++ tailWord_5790791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790791).length < 2 ^ (prefixWord ++ tailWord_5790791).sum := by decide
  have hdescent : baseEnd_5790791 < baseStart_5790791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790804 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 6]
def baseStart_5790804 : Nat := 118140960795 + 5790804 * 2 ^ 59
def prefixEnd_5790804 : Nat := 4983230072969 + 3 ^ 40 * 5790804 * 2
def baseEnd_5790804 : Nat := 330385091997629631824287

theorem tailTrace_5790804 : CollatzResearch.WordTrace tailWord_5790804 prefixEnd_5790804 330385091997629631824287 := by
  unfold tailWord_5790804
  simp only [CollatzResearch.WordTrace]
  refine ⟨105603986656456786715373733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140805315541942382287164977 105603986656456786715373733)
  ·
    refine ⟨19800747498085647509132575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105603986656456786715373733 19800747498085647509132575)
    ·
      refine ⟨29701121247128471263698863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19800747498085647509132575 29701121247128471263698863)
      ·
        refine ⟨44551681870692706895548295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29701121247128471263698863 44551681870692706895548295)
        ·
          refine ⟨66827522806039060343322443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44551681870692706895548295 66827522806039060343322443)
          ·
            refine ⟨100241284209058590514983665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66827522806039060343322443 100241284209058590514983665)
            ·
              refine ⟨75180963156793942886237749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100241284209058590514983665 75180963156793942886237749)
              ·
                refine ⟨7048215295949432145584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75180963156793942886237749 7048215295949432145584789)
                ·
                  refine ⟨330385091997629631824287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7048215295949432145584789 330385091997629631824287)
                  ·
                    rfl

theorem cell23_5790804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_5790804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790804 prefixEnd_5790804 := by exact prefixLift 5790804
  have htrace : WordTrace (prefixWord ++ tailWord_5790804) baseStart_5790804 baseEnd_5790804 := by
    simpa [prefixWord, tailWord_5790804, baseEnd_5790804] using wordTrace_append hprefix tailTrace_5790804
  have hstable : (prefixWord ++ tailWord_5790804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790804).length < 2 ^ (prefixWord ++ tailWord_5790804).sum := by decide
  have hdescent : baseEnd_5790804 < baseStart_5790804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790807 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5790807 : Nat := 118140960795 + 5790807 * 2 ^ 59
def prefixEnd_5790807 : Nat := 4983230072969 + 3 ^ 40 * 5790807 * 2
def baseEnd_5790807 : Nat := 2973467368420630174681069

theorem tailTrace_5790807 : CollatzResearch.WordTrace tailWord_5790807 prefixEnd_5790807 2973467368420630174681069 := by
  unfold tailWord_5790807
  simp only [CollatzResearch.WordTrace]
  refine ⟨211208082731902704943106675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140805388487935136628737783 211208082731902704943106675)
  ·
    refine ⟨316812124097854057414660013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211208082731902704943106675 316812124097854057414660013)
    ·
      refine ⟨118804546536695271530497505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316812124097854057414660013 118804546536695271530497505)
      ·
        refine ⟨89103409902521453647873129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118804546536695271530497505 89103409902521453647873129)
        ·
          refine ⟨66827557426891090235904847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89103409902521453647873129 66827557426891090235904847)
          ·
            refine ⟨100241336140336635353857271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66827557426891090235904847 100241336140336635353857271)
            ·
              refine ⟨150362004210504953030785907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100241336140336635353857271 150362004210504953030785907)
              ·
                refine ⟨225543006315757429546178861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150362004210504953030785907 225543006315757429546178861)
                ·
                  refine ⟨84578627368409036079817073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225543006315757429546178861 84578627368409036079817073)
                  ·
                    refine ⟨63433970526306777059862805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84578627368409036079817073 63433970526306777059862805)
                    ·
                      refine ⟨2973467368420630174681069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63433970526306777059862805 2973467368420630174681069)
                      ·
                        rfl

theorem cell23_5790807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5790807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790807 prefixEnd_5790807 := by exact prefixLift 5790807
  have htrace : WordTrace (prefixWord ++ tailWord_5790807) baseStart_5790807 baseEnd_5790807 := by
    simpa [prefixWord, tailWord_5790807, baseEnd_5790807] using wordTrace_append hprefix tailTrace_5790807
  have hstable : (prefixWord ++ tailWord_5790807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790807).length < 2 ^ (prefixWord ++ tailWord_5790807).sum := by decide
  have hdescent : baseEnd_5790807 < baseStart_5790807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790848 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 1, 1, 3]
def baseStart_5790848 : Nat := 118140960795 + 5790848 * 2 ^ 59
def prefixEnd_5790848 : Nat := 4983230072969 + 3 ^ 40 * 5790848 * 2
def baseEnd_5790848 : Nat := 2973488421127464514268381

theorem tailTrace_5790848 : CollatzResearch.WordTrace tailWord_5790848 prefixEnd_5790848 2973488421127464514268381 := by
  unfold tailWord_5790848
  simp only [CollatzResearch.WordTrace]
  refine ⟨105604789062377084472674599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140806385416502779296899465 105604789062377084472674599)
  ·
    refine ⟨158407183593565626709011899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105604789062377084472674599 158407183593565626709011899)
    ·
      refine ⟨237610775390348440063517849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158407183593565626709011899 237610775390348440063517849)
      ·
        refine ⟨178208081542761330047638387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237610775390348440063517849 178208081542761330047638387)
        ·
          refine ⟨267312122314141995071457581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178208081542761330047638387 267312122314141995071457581)
          ·
            refine ⟨100242045867803248151796593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267312122314141995071457581 100242045867803248151796593)
            ·
              refine ⟨75181534400852436113847445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100242045867803248151796593 75181534400852436113847445)
              ·
                refine ⟨3524134425039957942836599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75181534400852436113847445 3524134425039957942836599)
                ·
                  refine ⟨5286201637559936914254899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524134425039957942836599 5286201637559936914254899)
                  ·
                    refine ⟨7929302456339905371382349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286201637559936914254899 7929302456339905371382349)
                    ·
                      refine ⟨2973488421127464514268381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929302456339905371382349 2973488421127464514268381)
                      ·
                        rfl

theorem cell23_5790848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_5790848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790848 prefixEnd_5790848 := by exact prefixLift 5790848
  have htrace : WordTrace (prefixWord ++ tailWord_5790848) baseStart_5790848 baseEnd_5790848 := by
    simpa [prefixWord, tailWord_5790848, baseEnd_5790848] using wordTrace_append hprefix tailTrace_5790848
  have hstable : (prefixWord ++ tailWord_5790848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790848).length < 2 ^ (prefixWord ++ tailWord_5790848).sum := by decide
  have hdescent : baseEnd_5790848 < baseStart_5790848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790864 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_5790864 : Nat := 118140960795 + 5790864 * 2 ^ 59
def prefixEnd_5790864 : Nat := 4983230072969 + 3 ^ 40 * 5790864 * 2
def baseEnd_5790864 : Nat := 991165545605978817222769

theorem tailTrace_5790864 : CollatzResearch.WordTrace tailWord_5790864 prefixEnd_5790864 991165545605978817222769 := by
  unfold tailWord_5790864
  simp only [CollatzResearch.WordTrace]
  refine ⟨105605080846348101838965823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140806774461797469118621097 105605080846348101838965823)
  ·
    refine ⟨158407621269522152758448735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105605080846348101838965823 158407621269522152758448735)
    ·
      refine ⟨237611431904283229137673103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158407621269522152758448735 237611431904283229137673103)
      ·
        refine ⟨356417147856424843706509655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237611431904283229137673103 356417147856424843706509655)
        ·
          refine ⟨534625721784637265559764483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356417147856424843706509655 534625721784637265559764483)
          ·
            refine ⟨801938582676955898339646725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534625721784637265559764483 801938582676955898339646725)
            ·
              refine ⟨150363484251929230938683761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 801938582676955898339646725 150363484251929230938683761)
              ·
                refine ⟨112772613188946923204012821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150363484251929230938683761 112772613188946923204012821)
                ·
                  refine ⟨5286216243231887025188101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112772613188946923204012821 5286216243231887025188101)
                  ·
                    refine ⟨991165545605978817222769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286216243231887025188101 991165545605978817222769)
                    ·
                      rfl

theorem cell23_5790864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_5790864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790864 prefixEnd_5790864 := by exact prefixLift 5790864
  have htrace : WordTrace (prefixWord ++ tailWord_5790864) baseStart_5790864 baseEnd_5790864 := by
    simpa [prefixWord, tailWord_5790864, baseEnd_5790864] using wordTrace_append hprefix tailTrace_5790864
  have hstable : (prefixWord ++ tailWord_5790864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790864).length < 2 ^ (prefixWord ++ tailWord_5790864).sum := by decide
  have hdescent : baseEnd_5790864 < baseStart_5790864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790871 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5790871 : Nat := 118140960795 + 5790871 * 2 ^ 59
def prefixEnd_5790871 : Nat := 4983230072969 + 3 ^ 40 * 5790871 * 2
def baseEnd_5790871 : Nat := 2973500231182517924280775

theorem tailTrace_5790871 : CollatzResearch.WordTrace tailWord_5790871 prefixEnd_5790871 2973500231182517924280775 := by
  unfold tailWord_5790871
  simp only [CollatzResearch.WordTrace]
  refine ⟨211210417003670843873436467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140806944669113895915624311 211210417003670843873436467)
  ·
    refine ⟨316815625505506265810154701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211210417003670843873436467 316815625505506265810154701)
    ·
      refine ⟨118805859564564849678808013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316815625505506265810154701 118805859564564849678808013)
      ·
        refine ⟨44552197336711818629553005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118805859564564849678808013 44552197336711818629553005)
        ·
          refine ⟨16707074001266931986082377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44552197336711818629553005 16707074001266931986082377)
          ·
            refine ⟨12530305500950198989561783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16707074001266931986082377 12530305500950198989561783)
            ·
              refine ⟨18795458251425298484342675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12530305500950198989561783 18795458251425298484342675)
              ·
                refine ⟨28193187377137947726514013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18795458251425298484342675 28193187377137947726514013)
                ·
                  refine ⟨10572445266426730397442755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28193187377137947726514013 10572445266426730397442755)
                  ·
                    refine ⟨15858667899640095596164133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10572445266426730397442755 15858667899640095596164133)
                    ·
                      refine ⟨2973500231182517924280775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15858667899640095596164133 2973500231182517924280775)
                      ·
                        rfl

theorem cell23_5790871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5790871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790871 prefixEnd_5790871 := by exact prefixLift 5790871
  have htrace : WordTrace (prefixWord ++ tailWord_5790871) baseStart_5790871 baseEnd_5790871 := by
    simpa [prefixWord, tailWord_5790871, baseEnd_5790871] using wordTrace_append hprefix tailTrace_5790871
  have hstable : (prefixWord ++ tailWord_5790871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790871).length < 2 ^ (prefixWord ++ tailWord_5790871).sum := by decide
  have hdescent : baseEnd_5790871 < baseStart_5790871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790894 : List Nat := [4, 1, 4, 14]
def baseStart_5790894 : Nat := 118140960795 + 5790894 * 2 ^ 59
def prefixEnd_5790894 : Nat := 4983230072969 + 3 ^ 40 * 5790894 * 2
def baseEnd_5790894 : Nat := 1359630562980142356787

theorem tailTrace_5790894 : CollatzResearch.WordTrace tailWord_5790894 prefixEnd_5790894 1359630562980142356787 := by
  unfold tailWord_5790894
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401406985323439850190467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140807503921725012534349157 26401406985323439850190467)
  ·
    refine ⟨39602110477985159775285701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26401406985323439850190467 39602110477985159775285701)
    ·
      refine ⟨7425395714622217457866069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39602110477985159775285701 7425395714622217457866069)
      ·
        refine ⟨1359630562980142356787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7425395714622217457866069 1359630562980142356787)
        ·
          rfl

theorem cell23_5790894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 14].length) (baseStart_5790894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790894 prefixEnd_5790894 := by exact prefixLift 5790894
  have htrace : WordTrace (prefixWord ++ tailWord_5790894) baseStart_5790894 baseEnd_5790894 := by
    simpa [prefixWord, tailWord_5790894, baseEnd_5790894] using wordTrace_append hprefix tailTrace_5790894
  have hstable : (prefixWord ++ tailWord_5790894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790894).length < 2 ^ (prefixWord ++ tailWord_5790894).sum := by decide
  have hdescent : baseEnd_5790894 < baseStart_5790894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790898 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_5790898 : Nat := 118140960795 + 5790898 * 2 ^ 59
def prefixEnd_5790898 : Nat := 4983230072969 + 3 ^ 40 * 5790898 * 2
def baseEnd_5790898 : Nat := 991171365053396439547717

theorem tailTrace_5790898 : CollatzResearch.WordTrace tailWord_5790898 prefixEnd_5790898 991171365053396439547717 := by
  unfold tailWord_5790898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52802850443643256871167337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140807601183048684989779565 52802850443643256871167337)
  ·
    refine ⟨39602137832732442653375503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52802850443643256871167337 39602137832732442653375503)
    ·
      refine ⟨59403206749098663980063255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39602137832732442653375503 59403206749098663980063255)
      ·
        refine ⟨89104810123647995970094883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59403206749098663980063255 89104810123647995970094883)
        ·
          refine ⟨133657215185471993955142325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89104810123647995970094883 133657215185471993955142325)
          ·
            refine ⟨12530363923637999433294593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133657215185471993955142325 12530363923637999433294593)
            ·
              refine ⟨9397772942728499574970945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12530363923637999433294593 9397772942728499574970945)
              ·
                refine ⟨7048329707046374681228209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9397772942728499574970945 7048329707046374681228209)
                ·
                  refine ⟨5286247280284781010921157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048329707046374681228209 5286247280284781010921157)
                  ·
                    refine ⟨991171365053396439547717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286247280284781010921157 991171365053396439547717)
                    ·
                      rfl

theorem cell23_5790898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_5790898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790898 prefixEnd_5790898 := by exact prefixLift 5790898
  have htrace : WordTrace (prefixWord ++ tailWord_5790898) baseStart_5790898 baseEnd_5790898 := by
    simpa [prefixWord, tailWord_5790898, baseEnd_5790898] using wordTrace_append hprefix tailTrace_5790898
  have hstable : (prefixWord ++ tailWord_5790898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790898).length < 2 ^ (prefixWord ++ tailWord_5790898).sum := by decide
  have hdescent : baseEnd_5790898 < baseStart_5790898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790955 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 3]
def baseStart_5790955 : Nat := 118140960795 + 5790955 * 2 ^ 59
def prefixEnd_5790955 : Nat := 4983230072969 + 3 ^ 40 * 5790955 * 2
def baseEnd_5790955 : Nat := 2973543363557495595630389

theorem tailTrace_5790955 : CollatzResearch.WordTrace tailWord_5790955 prefixEnd_5790955 2973543363557495595630389 := by
  unfold tailWord_5790955
  simp only [CollatzResearch.WordTrace]
  refine ⟨211213480735366526219494319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140808987156911017479662879 211213480735366526219494319)
  ·
    refine ⟨316820221103049789329241479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211213480735366526219494319 316820221103049789329241479)
    ·
      refine ⟨475230331654574683993862219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316820221103049789329241479 475230331654574683993862219)
      ·
        refine ⟨712845497481862025990793329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475230331654574683993862219 712845497481862025990793329)
        ·
          refine ⟨534634123111396519493094997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712845497481862025990793329 534634123111396519493094997)
          ·
            refine ⟨6265243630211677962809707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 534634123111396519493094997 6265243630211677962809707)
            ·
              refine ⟨9397865445317516944214561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265243630211677962809707 9397865445317516944214561)
              ·
                refine ⟨7048399083988137708160921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9397865445317516944214561 7048399083988137708160921)
                ·
                  refine ⟨5286299312991103281120691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048399083988137708160921 5286299312991103281120691)
                  ·
                    refine ⟨7929448969486654921681037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286299312991103281120691 7929448969486654921681037)
                    ·
                      refine ⟨2973543363557495595630389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929448969486654921681037 2973543363557495595630389)
                      ·
                        rfl

theorem cell23_5790955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 3].length) (baseStart_5790955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790955 prefixEnd_5790955 := by exact prefixLift 5790955
  have htrace : WordTrace (prefixWord ++ tailWord_5790955) baseStart_5790955 baseEnd_5790955 := by
    simpa [prefixWord, tailWord_5790955, baseEnd_5790955] using wordTrace_append hprefix tailTrace_5790955
  have hstable : (prefixWord ++ tailWord_5790955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790955).length < 2 ^ (prefixWord ++ tailWord_5790955).sum := by decide
  have hdescent : baseEnd_5790955 < baseStart_5790955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790972 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_5790972 : Nat := 118140960795 + 5790972 * 2 ^ 59
def prefixEnd_5790972 : Nat := 4983230072969 + 3 ^ 40 * 5790972 * 2
def baseEnd_5790972 : Nat := 2973552092728622029117811

theorem tailTrace_5790972 : CollatzResearch.WordTrace tailWord_5790972 prefixEnd_5790972 2973552092728622029117811 := by
  unfold tailWord_5790972
  simp only [CollatzResearch.WordTrace]
  refine ⟨105607050388152469061431585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140809400517536625415242113 105607050388152469061431585)
  ·
    refine ⟨79205287791114351796073689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105607050388152469061431585 79205287791114351796073689)
    ·
      refine ⟨59403965843335763847055267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79205287791114351796073689 59403965843335763847055267)
      ·
        refine ⟨89105948765003645770582901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59403965843335763847055267 89105948765003645770582901)
        ·
          refine ⟨8353682696719091790992147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89105948765003645770582901 8353682696719091790992147)
          ·
            refine ⟨12530524045078637686488221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353682696719091790992147 12530524045078637686488221)
            ·
              refine ⟨4698946516904489132433083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12530524045078637686488221 4698946516904489132433083)
              ·
                refine ⟨7048419775356733698649625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698946516904489132433083 7048419775356733698649625)
                ·
                  refine ⟨5286314831517550273987219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048419775356733698649625 5286314831517550273987219)
                  ·
                    refine ⟨7929472247276325410980829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286314831517550273987219 7929472247276325410980829)
                    ·
                      refine ⟨2973552092728622029117811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929472247276325410980829 2973552092728622029117811)
                      ·
                        rfl

theorem cell23_5790972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_5790972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5790972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5790972 prefixEnd_5790972 := by exact prefixLift 5790972
  have htrace : WordTrace (prefixWord ++ tailWord_5790972) baseStart_5790972 baseEnd_5790972 := by
    simpa [prefixWord, tailWord_5790972, baseEnd_5790972] using wordTrace_append hprefix tailTrace_5790972
  have hstable : (prefixWord ++ tailWord_5790972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790972).length < 2 ^ (prefixWord ++ tailWord_5790972).sum := by decide
  have hdescent : baseEnd_5790972 < baseStart_5790972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791018 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_5791018 : Nat := 118140960795 + 5791018 * 2 ^ 59
def prefixEnd_5791018 : Nat := 4983230072969 + 3 ^ 40 * 5791018 * 2
def baseEnd_5791018 : Nat := 330397301426525427682511

theorem tailTrace_5791018 : CollatzResearch.WordTrace tailWord_5791018 prefixEnd_5791018 330397301426525427682511 := by
  unfold tailWord_5791018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52803944633534571994759427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140810519022758858652691805 52803944633534571994759427)
  ·
    refine ⟨79205916950301857992139141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52803944633534571994759427 79205916950301857992139141)
    ·
      refine ⟨14851109428181598373526089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79205916950301857992139141 14851109428181598373526089)
      ·
        refine ⟨11138332071136198780144567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14851109428181598373526089 11138332071136198780144567)
        ·
          refine ⟨16707498106704298170216851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138332071136198780144567 16707498106704298170216851)
          ·
            refine ⟨25061247160056447255325277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16707498106704298170216851 25061247160056447255325277)
            ·
              refine ⟨9397967685021167720746979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25061247160056447255325277 9397967685021167720746979)
              ·
                refine ⟨14096951527531751581120469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397967685021167720746979 14096951527531751581120469)
                ·
                  refine ⟨330397301426525427682511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14096951527531751581120469 330397301426525427682511)
                  ·
                    rfl

theorem cell23_5791018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_5791018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791018 prefixEnd_5791018 := by exact prefixLift 5791018
  have htrace : WordTrace (prefixWord ++ tailWord_5791018) baseStart_5791018 baseEnd_5791018 := by
    simpa [prefixWord, tailWord_5791018, baseEnd_5791018] using wordTrace_append hprefix tailTrace_5791018
  have hstable : (prefixWord ++ tailWord_5791018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791018).length < 2 ^ (prefixWord ++ tailWord_5791018).sum := by decide
  have hdescent : baseEnd_5791018 < baseStart_5791018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791028 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_5791028 : Nat := 118140960795 + 5791028 * 2 ^ 59
def prefixEnd_5791028 : Nat := 4983230072969 + 3 ^ 40 * 5791028 * 2
def baseEnd_5791028 : Nat := 2973580847645273810017553

theorem tailTrace_5791028 : CollatzResearch.WordTrace tailWord_5791028 prefixEnd_5791028 2973580847645273810017553 := by
  unfold tailWord_5791028
  simp only [CollatzResearch.WordTrace]
  refine ⟨105608071632051029843450869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140810762176068039791267825 105608071632051029843450869)
  ·
    refine ⟨9900756715504784047823519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105608071632051029843450869 9900756715504784047823519)
    ·
      refine ⟨14851135073257176071735279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900756715504784047823519 14851135073257176071735279)
      ·
        refine ⟨22276702609885764107602919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14851135073257176071735279 22276702609885764107602919)
        ·
          refine ⟨33415053914828646161404379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22276702609885764107602919 33415053914828646161404379)
          ·
            refine ⟨50122580872242969242106569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33415053914828646161404379 50122580872242969242106569)
            ·
              refine ⟨37591935654182226931579927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50122580872242969242106569 37591935654182226931579927)
              ·
                refine ⟨56387903481273340397369891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37591935654182226931579927 56387903481273340397369891)
                ·
                  refine ⟨84581855221910010596054837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56387903481273340397369891 84581855221910010596054837)
                  ·
                    refine ⟨7929548927054063493380141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84581855221910010596054837 7929548927054063493380141)
                    ·
                      refine ⟨2973580847645273810017553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929548927054063493380141 2973580847645273810017553)
                      ·
                        rfl

theorem cell23_5791028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_5791028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791028 prefixEnd_5791028 := by exact prefixLift 5791028
  have htrace : WordTrace (prefixWord ++ tailWord_5791028) baseStart_5791028 baseEnd_5791028 := by
    simpa [prefixWord, tailWord_5791028, baseEnd_5791028] using wordTrace_append hprefix tailTrace_5791028
  have hstable : (prefixWord ++ tailWord_5791028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791028).length < 2 ^ (prefixWord ++ tailWord_5791028).sum := by decide
  have hdescent : baseEnd_5791028 < baseStart_5791028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791029 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_5791029 : Nat := 118140960795 + 5791029 * 2 ^ 59
def prefixEnd_5791029 : Nat := 4983230072969 + 3 ^ 40 * 5791029 * 2
def baseEnd_5791029 : Nat := 2973581361125928306105049

theorem tailTrace_5791029 : CollatzResearch.WordTrace tailWord_5791029 prefixEnd_5791029 2973581361125928306105049 := by
  unfold tailWord_5791029
  simp only [CollatzResearch.WordTrace]
  refine ⟨211216179737098436857688141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140810786491398957905125427 211216179737098436857688141)
  ·
    refine ⟨79206067401411913821633053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211216179737098436857688141 79206067401411913821633053)
    ·
      refine ⟨29702275275529467683112395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79206067401411913821633053 29702275275529467683112395)
      ·
        refine ⟨44553412913294201524668593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29702275275529467683112395 44553412913294201524668593)
        ·
          refine ⟨33415059684970651143501445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44553412913294201524668593 33415059684970651143501445)
          ·
            refine ⟨6265323690931997089406521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33415059684970651143501445 6265323690931997089406521)
            ·
              refine ⟨4698992768198997817054891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6265323690931997089406521 4698992768198997817054891)
              ·
                refine ⟨7048489152298496725582337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698992768198997817054891 7048489152298496725582337)
                ·
                  refine ⟨5286366864223872544186753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048489152298496725582337 5286366864223872544186753)
                  ·
                    refine ⟨3964775148167904408140065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286366864223872544186753 3964775148167904408140065)
                    ·
                      refine ⟨2973581361125928306105049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964775148167904408140065 2973581361125928306105049)
                      ·
                        rfl

theorem cell23_5791029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_5791029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791029 prefixEnd_5791029 := by exact prefixLift 5791029
  have htrace : WordTrace (prefixWord ++ tailWord_5791029) baseStart_5791029 baseEnd_5791029 := by
    simpa [prefixWord, tailWord_5791029, baseEnd_5791029] using wordTrace_append hprefix tailTrace_5791029
  have hstable : (prefixWord ++ tailWord_5791029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791029).length < 2 ^ (prefixWord ++ tailWord_5791029).sum := by decide
  have hdescent : baseEnd_5791029 < baseStart_5791029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791069 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 5]
def baseStart_5791069 : Nat := 118140960795 + 5791069 * 2 ^ 59
def prefixEnd_5791069 : Nat := 4983230072969 + 3 ^ 40 * 5791069 * 2
def baseEnd_5791069 : Nat := 330400211150234238844985

theorem tailTrace_5791069 : CollatzResearch.WordTrace tailWord_5791069 prefixEnd_5791069 330400211150234238844985 := by
  unfold tailWord_5791069
  simp only [CollatzResearch.WordTrace]
  refine ⟨211217638656953523689144261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140811759104635682459429507 211217638656953523689144261)
  ·
    refine ⟨39603307248178785691714549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211217638656953523689144261 39603307248178785691714549)
    ·
      refine ⟨3712810054516761158598239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39603307248178785691714549 3712810054516761158598239)
      ·
        refine ⟨5569215081775141737897359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712810054516761158598239 5569215081775141737897359)
        ·
          refine ⟨8353822622662712606846039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569215081775141737897359 8353822622662712606846039)
          ·
            refine ⟨12530733933994068910269059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353822622662712606846039 12530733933994068910269059)
            ·
              refine ⟨18796100900991103365403589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12530733933994068910269059 18796100900991103365403589)
              ·
                refine ⟨3524268918935831881013173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18796100900991103365403589 3524268918935831881013173)
                ·
                  refine ⟨330400211150234238844985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524268918935831881013173 330400211150234238844985)
                  ·
                    rfl

theorem cell23_5791069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_5791069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791069 prefixEnd_5791069 := by exact prefixLift 5791069
  have htrace : WordTrace (prefixWord ++ tailWord_5791069) baseStart_5791069 baseEnd_5791069 := by
    simpa [prefixWord, tailWord_5791069, baseEnd_5791069] using wordTrace_append hprefix tailTrace_5791069
  have hstable : (prefixWord ++ tailWord_5791069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791069).length < 2 ^ (prefixWord ++ tailWord_5791069).sum := by decide
  have hdescent : baseEnd_5791069 < baseStart_5791069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791071 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_5791071 : Nat := 118140960795 + 5791071 * 2 ^ 59
def prefixEnd_5791071 : Nat := 4983230072969 + 3 ^ 40 * 5791071 * 2
def baseEnd_5791071 : Nat := 2973602927313417141779855

theorem tailTrace_5791071 : CollatzResearch.WordTrace tailWord_5791071 prefixEnd_5791071 2973602927313417141779855 := by
  unfold tailWord_5791071
  simp only [CollatzResearch.WordTrace]
  refine ⟨211217711602946278030717067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140811807735297518687144711 211217711602946278030717067)
  ·
    refine ⟨316826567404419417046075601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211217711602946278030717067 316826567404419417046075601)
    ·
      refine ⟨237619925553314562784556701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316826567404419417046075601 237619925553314562784556701)
      ·
        refine ⟨89107472082492961044208763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237619925553314562784556701 89107472082492961044208763)
        ·
          refine ⟨133661208123739441566313145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89107472082492961044208763 133661208123739441566313145)
          ·
            refine ⟨100245906092804581174734859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133661208123739441566313145 100245906092804581174734859)
            ·
              refine ⟨150368859139206871762102289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100245906092804581174734859 150368859139206871762102289)
              ·
                refine ⟨112776644354405153821576717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150368859139206871762102289 112776644354405153821576717)
                ·
                  refine ⟨42291241632901932683091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112776644354405153821576717 42291241632901932683091269)
                  ·
                    refine ⟨7929607806169112378079613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42291241632901932683091269 7929607806169112378079613)
                    ·
                      refine ⟨2973602927313417141779855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929607806169112378079613 2973602927313417141779855)
                      ·
                        rfl

theorem cell23_5791071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_5791071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791071 prefixEnd_5791071 := by exact prefixLift 5791071
  have htrace : WordTrace (prefixWord ++ tailWord_5791071) baseStart_5791071 baseEnd_5791071 := by
    simpa [prefixWord, tailWord_5791071, baseEnd_5791071] using wordTrace_append hprefix tailTrace_5791071
  have hstable : (prefixWord ++ tailWord_5791071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791071).length < 2 ^ (prefixWord ++ tailWord_5791071).sum := by decide
  have hdescent : baseEnd_5791071 < baseStart_5791071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791085 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_5791085 : Nat := 118140960795 + 5791085 * 2 ^ 59
def prefixEnd_5791085 : Nat := 4983230072969 + 3 ^ 40 * 5791085 * 2
def baseEnd_5791085 : Nat := 2973610116042580087004791

theorem tailTrace_5791085 : CollatzResearch.WordTrace tailWord_5791085 prefixEnd_5791085 2973610116042580087004791 := by
  unfold tailWord_5791085
  simp only [CollatzResearch.WordTrace]
  refine ⟨211218222224895558421726709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140812148149930372281151139 211218222224895558421726709)
  ·
    refine ⟨19801708333583958602036879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211218222224895558421726709 19801708333583958602036879)
    ·
      refine ⟨29702562500375937903055319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19801708333583958602036879 29702562500375937903055319)
      ·
        refine ⟨44553843750563906854582979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29702562500375937903055319 44553843750563906854582979)
        ·
          refine ⟨66830765625845860281874469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44553843750563906854582979 66830765625845860281874469)
          ·
            refine ⟨12530768554846098802851463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66830765625845860281874469 12530768554846098802851463)
            ·
              refine ⟨18796152832269148204277195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12530768554846098802851463 18796152832269148204277195)
              ·
                refine ⟨28194229248403722306415793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18796152832269148204277195 28194229248403722306415793)
                ·
                  refine ⟨21145671936302791729811845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28194229248403722306415793 21145671936302791729811845)
                  ·
                    refine ⟨3964813488056773449339721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21145671936302791729811845 3964813488056773449339721)
                    ·
                      refine ⟨2973610116042580087004791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964813488056773449339721 2973610116042580087004791)
                      ·
                        rfl

theorem cell23_5791085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_5791085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791085 prefixEnd_5791085 := by exact prefixLift 5791085
  have htrace : WordTrace (prefixWord ++ tailWord_5791085) baseStart_5791085 baseEnd_5791085 := by
    simpa [prefixWord, tailWord_5791085, baseEnd_5791085] using wordTrace_append hprefix tailTrace_5791085
  have hstable : (prefixWord ++ tailWord_5791085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791085).length < 2 ^ (prefixWord ++ tailWord_5791085).sum := by decide
  have hdescent : baseEnd_5791085 < baseStart_5791085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791102 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5791102 : Nat := 118140960795 + 5791102 * 2 ^ 59
def prefixEnd_5791102 : Nat := 4983230072969 + 3 ^ 40 * 5791102 * 2
def baseEnd_5791102 : Nat := 2973618845213706520492213

theorem tailTrace_5791102 : CollatzResearch.WordTrace tailWord_5791102 prefixEnd_5791102 2973618845213706520492213 := by
  unfold tailWord_5791102
  simp only [CollatzResearch.WordTrace]
  refine ⟨26402355283229246290636945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140812561510555980216730373 26402355283229246290636945)
  ·
    refine ⟨19801766462421934717977709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26402355283229246290636945 19801766462421934717977709)
    ·
      refine ⟨7425662423408225519241641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19801766462421934717977709 7425662423408225519241641)
      ·
        refine ⟨5569246817556169139431231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7425662423408225519241641 5569246817556169139431231)
        ·
          refine ⟨8353870226334253709146847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569246817556169139431231 8353870226334253709146847)
          ·
            refine ⟨12530805339501380563720271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353870226334253709146847 12530805339501380563720271)
            ·
              refine ⟨18796208009252070845580407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12530805339501380563720271 18796208009252070845580407)
              ·
                refine ⟨28194312013878106268370611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18796208009252070845580407 28194312013878106268370611)
                ·
                  refine ⟨42291468020817159402555917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28194312013878106268370611 42291468020817159402555917)
                  ·
                    refine ⟨15859300507806434775958469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42291468020817159402555917 15859300507806434775958469)
                    ·
                      refine ⟨2973618845213706520492213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15859300507806434775958469 2973618845213706520492213)
                      ·
                        rfl

theorem cell23_5791102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5791102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791102 prefixEnd_5791102 := by exact prefixLift 5791102
  have htrace : WordTrace (prefixWord ++ tailWord_5791102) baseStart_5791102 baseEnd_5791102 := by
    simpa [prefixWord, tailWord_5791102, baseEnd_5791102] using wordTrace_append hprefix tailTrace_5791102
  have hstable : (prefixWord ++ tailWord_5791102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791102).length < 2 ^ (prefixWord ++ tailWord_5791102).sum := by decide
  have hdescent : baseEnd_5791102 < baseStart_5791102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791105 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_5791105 : Nat := 118140960795 + 5791105 * 2 ^ 59
def prefixEnd_5791105 : Nat := 4983230072969 + 3 ^ 40 * 5791105 * 2
def baseEnd_5791105 : Nat := 2973620385655670008754699

theorem tailTrace_5791105 : CollatzResearch.WordTrace tailWord_5791105 prefixEnd_5791105 2973620385655670008754699 := by
  unfold tailWord_5791105
  simp only [CollatzResearch.WordTrace]
  refine ⟨211218951684823101837454769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140812634456548734558303179 211218951684823101837454769)
  ·
    refine ⟨158414213763617326378091077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211218951684823101837454769 158414213763617326378091077)
    ·
      refine ⟨29702665080678248695892077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158414213763617326378091077 29702665080678248695892077)
      ·
        refine ⟨11138499405254343260959529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29702665080678248695892077 11138499405254343260959529)
        ·
          refine ⟨8353874553940757445719647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11138499405254343260959529 8353874553940757445719647)
          ·
            refine ⟨12530811830911136168579471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353874553940757445719647 12530811830911136168579471)
            ·
              refine ⟨18796217746366704252869207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12530811830911136168579471 18796217746366704252869207)
              ·
                refine ⟨28194326619550056379303811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18796217746366704252869207 28194326619550056379303811)
                ·
                  refine ⟨42291489929325084568955717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28194326619550056379303811 42291489929325084568955717)
                  ·
                    refine ⟨7929654361748453356679197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42291489929325084568955717 7929654361748453356679197)
                    ·
                      refine ⟨2973620385655670008754699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929654361748453356679197 2973620385655670008754699)
                      ·
                        rfl

theorem cell23_5791105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_5791105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791105 prefixEnd_5791105 := by exact prefixLift 5791105
  have htrace : WordTrace (prefixWord ++ tailWord_5791105) baseStart_5791105 baseEnd_5791105 := by
    simpa [prefixWord, tailWord_5791105, baseEnd_5791105] using wordTrace_append hprefix tailTrace_5791105
  have hstable : (prefixWord ++ tailWord_5791105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791105).length < 2 ^ (prefixWord ++ tailWord_5791105).sum := by decide
  have hdescent : baseEnd_5791105 < baseStart_5791105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791112 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 1, 4]
def baseStart_5791112 : Nat := 118140960795 + 5791112 * 2 ^ 59
def prefixEnd_5791112 : Nat := 4983230072969 + 3 ^ 40 * 5791112 * 2
def baseEnd_5791112 : Nat := 991207993340083827122389

theorem tailTrace_5791112 : CollatzResearch.WordTrace tailWord_5791112 prefixEnd_5791112 991207993340083827122389 := by
  unfold tailWord_5791112
  simp only [CollatzResearch.WordTrace]
  refine ⟨105609603497898871016479795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140812804663865161355306393 105609603497898871016479795)
  ·
    refine ⟨158414405246848306524719693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105609603497898871016479795 158414405246848306524719693)
    ·
      refine ⟨59405401967568114946769885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158414405246848306524719693 59405401967568114946769885)
      ·
        refine ⟨22277025737838043105038707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59405401967568114946769885 22277025737838043105038707)
        ·
          refine ⟨33415538606757064657558061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22277025737838043105038707 33415538606757064657558061)
          ·
            refine ⟨12530826977533899246584273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33415538606757064657558061 12530826977533899246584273)
            ·
              refine ⟨9398120233150424434938205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12530826977533899246584273 9398120233150424434938205)
              ·
                refine ⟨3524295087431409163101827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9398120233150424434938205 3524295087431409163101827)
                ·
                  refine ⟨5286442631147113744652741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524295087431409163101827 5286442631147113744652741)
                  ·
                    refine ⟨991207993340083827122389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286442631147113744652741 991207993340083827122389)
                    ·
                      rfl

theorem cell23_5791112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_5791112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791112 prefixEnd_5791112 := by exact prefixLift 5791112
  have htrace : WordTrace (prefixWord ++ tailWord_5791112) baseStart_5791112 baseEnd_5791112 := by
    simpa [prefixWord, tailWord_5791112, baseEnd_5791112] using wordTrace_append hprefix tailTrace_5791112
  have hstable : (prefixWord ++ tailWord_5791112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791112).length < 2 ^ (prefixWord ++ tailWord_5791112).sum := by decide
  have hdescent : baseEnd_5791112 < baseStart_5791112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791135 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 3]
def baseStart_5791135 : Nat := 118140960795 + 5791135 * 2 ^ 59
def prefixEnd_5791135 : Nat := 4983230072969 + 3 ^ 40 * 5791135 * 2
def baseEnd_5791135 : Nat := 2973635790075304891379561

theorem tailTrace_5791135 : CollatzResearch.WordTrace tailWord_5791135 prefixEnd_5791135 2973635790075304891379561 := by
  unfold tailWord_5791135
  simp only [CollatzResearch.WordTrace]
  refine ⟨211220045874714416961046859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140813363916476277974031239 211220045874714416961046859)
  ·
    refine ⟨316830068812071625441570289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211220045874714416961046859 316830068812071625441570289)
    ·
      refine ⟨237622551609053719081177717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316830068812071625441570289 237622551609053719081177717)
      ·
        refine ⟨22277114213348786163860411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237622551609053719081177717 22277114213348786163860411)
        ·
          refine ⟨33415671320023179245790617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22277114213348786163860411 33415671320023179245790617)
          ·
            refine ⟨25061753490017384434342963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33415671320023179245790617 25061753490017384434342963)
            ·
              refine ⟨37592630235026076651514445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25061753490017384434342963 37592630235026076651514445)
              ·
                refine ⟨14097236338134778744317917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37592630235026076651514445 14097236338134778744317917)
                ·
                  refine ⟨5286463626800542029119219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14097236338134778744317917 5286463626800542029119219)
                  ·
                    refine ⟨7929695440200813043678829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286463626800542029119219 7929695440200813043678829)
                    ·
                      refine ⟨2973635790075304891379561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929695440200813043678829 2973635790075304891379561)
                      ·
                        rfl

theorem cell23_5791135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_5791135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791135 prefixEnd_5791135 := by exact prefixLift 5791135
  have htrace : WordTrace (prefixWord ++ tailWord_5791135) baseStart_5791135 baseEnd_5791135 := by
    simpa [prefixWord, tailWord_5791135, baseEnd_5791135] using wordTrace_append hprefix tailTrace_5791135
  have hstable : (prefixWord ++ tailWord_5791135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791135).length < 2 ^ (prefixWord ++ tailWord_5791135).sum := by decide
  have hdescent : baseEnd_5791135 < baseStart_5791135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791141 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_5791141 : Nat := 118140960795 + 5791141 * 2 ^ 59
def prefixEnd_5791141 : Nat := 4983230072969 + 3 ^ 40 * 5791141 * 2
def baseEnd_5791141 : Nat := 2973638870959231867904533

theorem tailTrace_5791141 : CollatzResearch.WordTrace tailWord_5791141 prefixEnd_5791141 2973638870959231867904533 := by
  unfold tailWord_5791141
  simp only [CollatzResearch.WordTrace]
  refine ⟨211220264712692679985765277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140813509808461786657176851 211220264712692679985765277)
  ·
    refine ⟨79207599267259754994661979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211220264712692679985765277 79207599267259754994661979)
    ·
      refine ⟨118811398900889632491992969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79207599267259754994661979 118811398900889632491992969)
      ·
        refine ⟨89108549175667224368994727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118811398900889632491992969 89108549175667224368994727)
        ·
          refine ⟨133662823763500836553492091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89108549175667224368994727 133662823763500836553492091)
          ·
            refine ⟨200494235645251254830238137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133662823763500836553492091 200494235645251254830238137)
            ·
              refine ⟨150370676733938441122678603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200494235645251254830238137 150370676733938441122678603)
              ·
                refine ⟨225556015100907661684017905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150370676733938441122678603 225556015100907661684017905)
                ·
                  refine ⟨169167011325680746263013429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225556015100907661684017905 169167011325680746263013429)
                  ·
                    refine ⟨15859407311782569962157509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169167011325680746263013429 15859407311782569962157509)
                    ·
                      refine ⟨2973638870959231867904533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15859407311782569962157509 2973638870959231867904533)
                      ·
                        rfl

theorem cell23_5791141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_5791141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791141 prefixEnd_5791141 := by exact prefixLift 5791141
  have htrace : WordTrace (prefixWord ++ tailWord_5791141) baseStart_5791141 baseEnd_5791141 := by
    simpa [prefixWord, tailWord_5791141, baseEnd_5791141] using wordTrace_append hprefix tailTrace_5791141
  have hstable : (prefixWord ++ tailWord_5791141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791141).length < 2 ^ (prefixWord ++ tailWord_5791141).sum := by decide
  have hdescent : baseEnd_5791141 < baseStart_5791141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791168 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_5791168 : Nat := 118140960795 + 5791168 * 2 ^ 59
def prefixEnd_5791168 : Nat := 4983230072969 + 3 ^ 40 * 5791168 * 2
def baseEnd_5791168 : Nat := 991217578312301087422303

theorem tailTrace_5791168 : CollatzResearch.WordTrace tailWord_5791168 prefixEnd_5791168 991217578312301087422303 := by
  unfold tailWord_5791168
  simp only [CollatzResearch.WordTrace]
  refine ⟨105610624741797431798499079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140814166322396575731332105 105610624741797431798499079)
  ·
    refine ⟨158415937112696147697748619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105610624741797431798499079 158415937112696147697748619)
    ·
      refine ⟨237623905669044221546622929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158415937112696147697748619 237623905669044221546622929)
      ·
        refine ⟨178217929251783166159967197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237623905669044221546622929 178217929251783166159967197)
        ·
          refine ⟨66831723469418687309987699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178217929251783166159967197 66831723469418687309987699)
          ·
            refine ⟨100247585204128030964981549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66831723469418687309987699 100247585204128030964981549)
            ·
              refine ⟨37592844451548011611868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100247585204128030964981549 37592844451548011611868081)
              ·
                refine ⟨28194633338661008708901061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37592844451548011611868081 28194633338661008708901061)
                ·
                  refine ⟨5286493750998939132918949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28194633338661008708901061 5286493750998939132918949)
                  ·
                    refine ⟨991217578312301087422303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286493750998939132918949 991217578312301087422303)
                    ·
                      rfl

theorem cell23_5791168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_5791168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791168 prefixEnd_5791168 := by exact prefixLift 5791168
  have htrace : WordTrace (prefixWord ++ tailWord_5791168) baseStart_5791168 baseEnd_5791168 := by
    simpa [prefixWord, tailWord_5791168, baseEnd_5791168] using wordTrace_append hprefix tailTrace_5791168
  have hstable : (prefixWord ++ tailWord_5791168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791168).length < 2 ^ (prefixWord ++ tailWord_5791168).sum := by decide
  have hdescent : baseEnd_5791168 < baseStart_5791168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791178 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_5791178 : Nat := 118140960795 + 5791178 * 2 ^ 59
def prefixEnd_5791178 : Nat := 4983230072969 + 3 ^ 40 * 5791178 * 2
def baseEnd_5791178 : Nat := 2973657869743448223141863

theorem tailTrace_5791178 : CollatzResearch.WordTrace tailWord_5791178 prefixEnd_5791178 2973657869743448223141863 := by
  unfold tailWord_5791178
  simp only [CollatzResearch.WordTrace]
  refine ⟨52805403553389658826215547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140814409475705756869908125 52805403553389658826215547)
  ·
    refine ⟨79208105330084488239323321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52805403553389658826215547 79208105330084488239323321)
    ·
      refine ⟨59406078997563366179492491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79208105330084488239323321 59406078997563366179492491)
      ·
        refine ⟨89109118496345049269238737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59406078997563366179492491 89109118496345049269238737)
        ·
          refine ⟨66831838872258786951929053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89109118496345049269238737 66831838872258786951929053)
          ·
            refine ⟨25061939577097045106973395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66831838872258786951929053 25061939577097045106973395)
            ·
              refine ⟨37592909365645567660460093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25061939577097045106973395 37592909365645567660460093)
              ·
                refine ⟨14097341012117087872672535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37592909365645567660460093 14097341012117087872672535)
                ·
                  refine ⟨21146011518175631809008803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14097341012117087872672535 21146011518175631809008803)
                  ·
                    refine ⟨31719017277263447713513205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21146011518175631809008803 31719017277263447713513205)
                    ·
                      refine ⟨2973657869743448223141863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31719017277263447713513205 2973657869743448223141863)
                      ·
                        rfl

theorem cell23_5791178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_5791178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791178 prefixEnd_5791178 := by exact prefixLift 5791178
  have htrace : WordTrace (prefixWord ++ tailWord_5791178) baseStart_5791178 baseEnd_5791178 := by
    simpa [prefixWord, tailWord_5791178, baseEnd_5791178] using wordTrace_append hprefix tailTrace_5791178
  have hstable : (prefixWord ++ tailWord_5791178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791178).length < 2 ^ (prefixWord ++ tailWord_5791178).sum := by decide
  have hdescent : baseEnd_5791178 < baseStart_5791178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791192 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_5791192 : Nat := 118140960795 + 5791192 * 2 ^ 59
def prefixEnd_5791192 : Nat := 4983230072969 + 3 ^ 40 * 5791192 * 2
def baseEnd_5791192 : Nat := 2973665058472611168366799

theorem tailTrace_5791192 : CollatzResearch.WordTrace tailWord_5791192 prefixEnd_5791192 2973665058472611168366799 := by
  unfold tailWord_5791192
  simp only [CollatzResearch.WordTrace]
  refine ⟨105611062417753957847935915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140814749890338610463914553 105611062417753957847935915)
  ·
    refine ⟨158416593626630936771903873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105611062417753957847935915 158416593626630936771903873)
    ·
      refine ⟨118812445219973202578927905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158416593626630936771903873 118812445219973202578927905)
      ·
        refine ⟨89109333914979901934195929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118812445219973202578927905 89109333914979901934195929)
        ·
          refine ⟨66832000436234926450646947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89109333914979901934195929 66832000436234926450646947)
          ·
            refine ⟨100248000654352389675970421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66832000436234926450646947 100248000654352389675970421)
            ·
              refine ⟨9398250061345536532122227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100248000654352389675970421 9398250061345536532122227)
              ·
                refine ⟨14097375092018304798183341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9398250061345536532122227 14097375092018304798183341)
                ·
                  refine ⟨5286515659506864299318753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14097375092018304798183341 5286515659506864299318753)
                  ·
                    refine ⟨3964886744630148224489065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286515659506864299318753 3964886744630148224489065)
                    ·
                      refine ⟨2973665058472611168366799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964886744630148224489065 2973665058472611168366799)
                      ·
                        rfl

theorem cell23_5791192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_5791192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791192 prefixEnd_5791192 := by exact prefixLift 5791192
  have htrace : WordTrace (prefixWord ++ tailWord_5791192) baseStart_5791192 baseEnd_5791192 := by
    simpa [prefixWord, tailWord_5791192, baseEnd_5791192] using wordTrace_append hprefix tailTrace_5791192
  have hstable : (prefixWord ++ tailWord_5791192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791192).length < 2 ^ (prefixWord ++ tailWord_5791192).sum := by decide
  have hdescent : baseEnd_5791192 < baseStart_5791192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791211 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 7]
def baseStart_5791211 : Nat := 118140960795 + 5791211 * 2 ^ 59
def prefixEnd_5791211 : Nat := 4983230072969 + 3 ^ 40 * 5791211 * 2
def baseEnd_5791211 : Nat := 991224938201682198009737

theorem tailTrace_5791211 : CollatzResearch.WordTrace tailWord_5791211 prefixEnd_5791211 991224938201682198009737 := by
  unfold tailWord_5791211
  simp only [CollatzResearch.WordTrace]
  refine ⟨211222817822439081940813487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140815211881626054627208991 211222817822439081940813487)
  ·
    refine ⟨316834226733658622911220231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211222817822439081940813487 316834226733658622911220231)
    ·
      refine ⟨475251340100487934366830347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316834226733658622911220231 475251340100487934366830347)
      ·
        refine ⟨712877010150731901550245521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475251340100487934366830347 712877010150731901550245521)
        ·
          refine ⟨534657757613048926162684141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712877010150731901550245521 534657757613048926162684141)
          ·
            refine ⟨200496659104893347311006553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534657757613048926162684141 200496659104893347311006553)
            ·
              refine ⟨150372494328670010483254915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200496659104893347311006553 150372494328670010483254915)
              ·
                refine ⟨225558741493005015724882373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150372494328670010483254915 225558741493005015724882373)
                ·
                  refine ⟨42292264029938440448415445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225558741493005015724882373 42292264029938440448415445)
                  ·
                    refine ⟨991224938201682198009737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42292264029938440448415445 991224938201682198009737)
                    ·
                      rfl

theorem cell23_5791211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_5791211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791211 prefixEnd_5791211 := by exact prefixLift 5791211
  have htrace : WordTrace (prefixWord ++ tailWord_5791211) baseStart_5791211 baseEnd_5791211 := by
    simpa [prefixWord, tailWord_5791211, baseEnd_5791211] using wordTrace_append hprefix tailTrace_5791211
  have hstable : (prefixWord ++ tailWord_5791211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791211).length < 2 ^ (prefixWord ++ tailWord_5791211).sum := by decide
  have hdescent : baseEnd_5791211 < baseStart_5791211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791242 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_5791242 : Nat := 118140960795 + 5791242 * 2 ^ 59
def prefixEnd_5791242 : Nat := 4983230072969 + 3 ^ 40 * 5791242 * 2
def baseEnd_5791242 : Nat := 2973690732505335972741569

theorem tailTrace_5791242 : CollatzResearch.WordTrace tailWord_5791242 prefixEnd_5791242 2973690732505335972741569 := by
  unfold tailWord_5791242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52805987121331693558797995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140815965656884516156794653 52805987121331693558797995)
  ·
    refine ⟨79208980681997540338196993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52805987121331693558797995 79208980681997540338196993)
    ·
      refine ⟨59406735511498155253647745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79208980681997540338196993 59406735511498155253647745)
      ·
        refine ⟨44555051633623616440235809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59406735511498155253647745 44555051633623616440235809)
        ·
          refine ⟨33416288725217712330176857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44555051633623616440235809 33416288725217712330176857)
          ·
            refine ⟨25062216543913284247632643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33416288725217712330176857 25062216543913284247632643)
            ·
              refine ⟨37593324815869926371448965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25062216543913284247632643 37593324815869926371448965)
              ·
                refine ⟨7048748402975611194646681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37593324815869926371448965 7048748402975611194646681)
                ·
                  refine ⟨5286561302231708395985011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048748402975611194646681 5286561302231708395985011)
                  ·
                    refine ⟨7929841953347562593977517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286561302231708395985011 7929841953347562593977517)
                    ·
                      refine ⟨2973690732505335972741569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7929841953347562593977517 2973690732505335972741569)
                      ·
                        rfl

theorem cell23_5791242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_5791242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791242 prefixEnd_5791242 := by exact prefixLift 5791242
  have htrace : WordTrace (prefixWord ++ tailWord_5791242) baseStart_5791242 baseEnd_5791242 := by
    simpa [prefixWord, tailWord_5791242, baseEnd_5791242] using wordTrace_append hprefix tailTrace_5791242
  have hstable : (prefixWord ++ tailWord_5791242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791242).length < 2 ^ (prefixWord ++ tailWord_5791242).sum := by decide
  have hdescent : baseEnd_5791242 < baseStart_5791242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791243 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 1, 2, 2]
def baseStart_5791243 : Nat := 118140960795 + 5791243 * 2 ^ 59
def prefixEnd_5791243 : Nat := 4983230072969 + 3 ^ 40 * 5791243 * 2
def baseEnd_5791243 : Nat := 2973691245985990468829065

theorem tailTrace_5791243 : CollatzResearch.WordTrace tailWord_5791243 prefixEnd_5791243 2973691245985990468829065 := by
  unfold tailWord_5791243
  simp only [CollatzResearch.WordTrace]
  refine ⟨211223984958323151405978383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140815989972215434270652255 211223984958323151405978383)
  ·
    refine ⟨316835977437484727108967575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211223984958323151405978383 316835977437484727108967575)
    ·
      refine ⟨475253966156227090663451363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316835977437484727108967575 475253966156227090663451363)
      ·
        refine ⟨712880949234340635995177045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475253966156227090663451363 712880949234340635995177045)
        ·
          refine ⟨8354073623839929328068481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 712880949234340635995177045 8354073623839929328068481)
          ·
            refine ⟨6265555217879946996051361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8354073623839929328068481 6265555217879946996051361)
            ·
              refine ⟨4699166413409960247038521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6265555217879946996051361 4699166413409960247038521)
              ·
                refine ⟨3524374810057470185278891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699166413409960247038521 3524374810057470185278891)
                ·
                  refine ⟨5286562215086205277918337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524374810057470185278891 5286562215086205277918337)
                  ·
                    refine ⟨3964921661314653958438753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286562215086205277918337 3964921661314653958438753)
                    ·
                      refine ⟨2973691245985990468829065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964921661314653958438753 2973691245985990468829065)
                      ·
                        rfl

theorem cell23_5791243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 2, 2].length) (baseStart_5791243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791243 prefixEnd_5791243 := by exact prefixLift 5791243
  have htrace : WordTrace (prefixWord ++ tailWord_5791243) baseStart_5791243 baseEnd_5791243 := by
    simpa [prefixWord, tailWord_5791243, baseEnd_5791243] using wordTrace_append hprefix tailTrace_5791243
  have hstable : (prefixWord ++ tailWord_5791243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791243).length < 2 ^ (prefixWord ++ tailWord_5791243).sum := by decide
  have hdescent : baseEnd_5791243 < baseStart_5791243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791282 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_5791282 : Nat := 118140960795 + 5791282 * 2 ^ 59
def prefixEnd_5791282 : Nat := 4983230072969 + 3 ^ 40 * 5791282 * 2
def baseEnd_5791282 : Nat := 2973711271731515816241385

theorem tailTrace_5791282 : CollatzResearch.WordTrace tailWord_5791282 prefixEnd_5791282 2973711271731515816241385 := by
  unfold tailWord_5791282
  simp only [CollatzResearch.WordTrace]
  refine ⟨52806351851295465266662025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140816938270121240711098733 52806351851295465266662025)
  ·
    refine ⟨39604763888471598949996519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52806351851295465266662025 39604763888471598949996519)
    ·
      refine ⟨59407145832707398424994779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39604763888471598949996519 59407145832707398424994779)
      ·
        refine ⟨89110718749061097637492169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59407145832707398424994779 89110718749061097637492169)
        ·
          refine ⟨66833039061795823228119127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89110718749061097637492169 66833039061795823228119127)
          ·
            refine ⟨100249558592693734842178691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66833039061795823228119127 100249558592693734842178691)
            ·
              refine ⟨150374337889040602263268037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100249558592693734842178691 150374337889040602263268037)
              ·
                refine ⟨28195188354195112924362757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150374337889040602263268037 28195188354195112924362757)
                ·
                  refine ⟨5286597816411583673318017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28195188354195112924362757 5286597816411583673318017)
                  ·
                    refine ⟨3964948362308687754988513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286597816411583673318017 3964948362308687754988513)
                    ·
                      refine ⟨2973711271731515816241385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964948362308687754988513 2973711271731515816241385)
                      ·
                        rfl

theorem cell23_5791282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_5791282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791282 prefixEnd_5791282 := by exact prefixLift 5791282
  have htrace : WordTrace (prefixWord ++ tailWord_5791282) baseStart_5791282 baseEnd_5791282 := by
    simpa [prefixWord, tailWord_5791282, baseEnd_5791282] using wordTrace_append hprefix tailTrace_5791282
  have hstable : (prefixWord ++ tailWord_5791282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791282).length < 2 ^ (prefixWord ++ tailWord_5791282).sum := by decide
  have hdescent : baseEnd_5791282 < baseStart_5791282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791286 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_5791286 : Nat := 118140960795 + 5791286 * 2 ^ 59
def prefixEnd_5791286 : Nat := 4983230072969 + 3 ^ 40 * 5791286 * 2
def baseEnd_5791286 : Nat := 2973713325654133800591367

theorem tailTrace_5791286 : CollatzResearch.WordTrace tailWord_5791286 prefixEnd_5791286 2973713325654133800591367 := by
  unfold tailWord_5791286
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201597081072960609362107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140817035531444913166529141 13201597081072960609362107)
  ·
    refine ⟨19802395621609440914043161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13201597081072960609362107 19802395621609440914043161)
    ·
      refine ⟨14851796716207080685532371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19802395621609440914043161 14851796716207080685532371)
      ·
        refine ⟨22277695074310621028298557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14851796716207080685532371 22277695074310621028298557)
        ·
          refine ⟨8354135652866482885611959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22277695074310621028298557 8354135652866482885611959)
          ·
            refine ⟨12531203479299724328417939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8354135652866482885611959 12531203479299724328417939)
            ·
              refine ⟨18796805218949586492626909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12531203479299724328417939 18796805218949586492626909)
              ·
                refine ⟨7048801957106094934735091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18796805218949586492626909 7048801957106094934735091)
                ·
                  refine ⟨10573202935659142402102637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7048801957106094934735091 10573202935659142402102637)
                  ·
                    refine ⟨3964951100872178400788489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10573202935659142402102637 3964951100872178400788489)
                    ·
                      refine ⟨2973713325654133800591367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964951100872178400788489 2973713325654133800591367)
                      ·
                        rfl

theorem cell23_5791286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_5791286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791286 prefixEnd_5791286 := by exact prefixLift 5791286
  have htrace : WordTrace (prefixWord ++ tailWord_5791286) baseStart_5791286 baseEnd_5791286 := by
    simpa [prefixWord, tailWord_5791286, baseEnd_5791286] using wordTrace_append hprefix tailTrace_5791286
  have hstable : (prefixWord ++ tailWord_5791286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791286).length < 2 ^ (prefixWord ++ tailWord_5791286).sum := by decide
  have hdescent : baseEnd_5791286 < baseStart_5791286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791316 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_5791316 : Nat := 118140960795 + 5791316 * 2 ^ 59
def prefixEnd_5791316 : Nat := 4983230072969 + 3 ^ 40 * 5791316 * 2
def baseEnd_5791316 : Nat := 2973728730073768683216229

theorem tailTrace_5791316 : CollatzResearch.WordTrace tailWord_5791316 prefixEnd_5791316 2973728730073768683216229 := by
  unfold tailWord_5791316
  simp only [CollatzResearch.WordTrace]
  refine ⟨105613323743529342436692901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140817764991372456582257201 105613323743529342436692901)
  ·
    refine ⟨19802498201911751706879919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105613323743529342436692901 19802498201911751706879919)
    ·
      refine ⟨29703747302867627560319879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19802498201911751706879919 29703747302867627560319879)
      ·
        refine ⟨44555620954301441340479819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29703747302867627560319879 44555620954301441340479819)
        ·
          refine ⟨66833431431452162010719729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44555620954301441340479819 66833431431452162010719729)
          ·
            refine ⟨50125073573589121508039797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66833431431452162010719729 50125073573589121508039797)
            ·
              refine ⟨4699225647523980141378731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50125073573589121508039797 4699225647523980141378731)
              ·
                refine ⟨7048838471285970212068097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699225647523980141378731 7048838471285970212068097)
                ·
                  refine ⟨5286628853464477659051073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048838471285970212068097 5286628853464477659051073)
                  ·
                    refine ⟨3964971640098358244288305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286628853464477659051073 3964971640098358244288305)
                    ·
                      refine ⟨2973728730073768683216229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3964971640098358244288305 2973728730073768683216229)
                      ·
                        rfl

theorem cell23_5791316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_5791316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791316 prefixEnd_5791316 := by exact prefixLift 5791316
  have htrace : WordTrace (prefixWord ++ tailWord_5791316) baseStart_5791316 baseEnd_5791316 := by
    simpa [prefixWord, tailWord_5791316, baseEnd_5791316] using wordTrace_append hprefix tailTrace_5791316
  have hstable : (prefixWord ++ tailWord_5791316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791316).length < 2 ^ (prefixWord ++ tailWord_5791316).sum := by decide
  have hdescent : baseEnd_5791316 < baseStart_5791316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791328 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_5791328 : Nat := 118140960795 + 5791328 * 2 ^ 59
def prefixEnd_5791328 : Nat := 4983230072969 + 3 ^ 40 * 5791328 * 2
def baseEnd_5791328 : Nat := 2973734891841622636266173

theorem tailTrace_5791328 : CollatzResearch.WordTrace tailWord_5791328 prefixEnd_5791328 2973734891841622636266173 := by
  unfold tailWord_5791328
  simp only [CollatzResearch.WordTrace]
  refine ⟨105613542581507605461411319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140818056775343473948548425 105613542581507605461411319)
  ·
    refine ⟨158420313872261408192116979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105613542581507605461411319 158420313872261408192116979)
    ·
      refine ⟨237630470808392112288175469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158420313872261408192116979 237630470808392112288175469)
      ·
        refine ⟨89111426553147042108065801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237630470808392112288175469 89111426553147042108065801)
        ·
          refine ⟨66833569914860281581049351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89111426553147042108065801 66833569914860281581049351)
          ·
            refine ⟨100250354872290422371574027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66833569914860281581049351 100250354872290422371574027)
            ·
              refine ⟨150375532308435633557361041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100250354872290422371574027 150375532308435633557361041)
              ·
                refine ⟨112781649231326725168020781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150375532308435633557361041 112781649231326725168020781)
                ·
                  refine ⟨42293118461747521938007793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112781649231326725168020781 42293118461747521938007793)
                  ·
                    refine ⟨31719838846310641453505845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42293118461747521938007793 31719838846310641453505845)
                    ·
                      refine ⟨2973734891841622636266173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31719838846310641453505845 2973734891841622636266173)
                      ·
                        rfl

theorem cell23_5791328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_5791328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791328 prefixEnd_5791328 := by exact prefixLift 5791328
  have htrace : WordTrace (prefixWord ++ tailWord_5791328) baseStart_5791328 baseEnd_5791328 := by
    simpa [prefixWord, tailWord_5791328, baseEnd_5791328] using wordTrace_append hprefix tailTrace_5791328
  have hstable : (prefixWord ++ tailWord_5791328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791328).length < 2 ^ (prefixWord ++ tailWord_5791328).sum := by decide
  have hdescent : baseEnd_5791328 < baseStart_5791328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791355 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4]
def baseStart_5791355 : Nat := 118140960795 + 5791355 * 2 ^ 59
def prefixEnd_5791355 : Nat := 4983230072969 + 3 ^ 40 * 5791355 * 2
def baseEnd_5791355 : Nat := 2973748755819294030628549

theorem tailTrace_5791355 : CollatzResearch.WordTrace tailWord_5791355 prefixEnd_5791355 2973748755819294030628549 := by
  unfold tailWord_5791355
  simp only [CollatzResearch.WordTrace]
  refine ⟨211228069933917394534055519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140818713289278263022703679 211228069933917394534055519)
  ·
    refine ⟨316842104900876091801083279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211228069933917394534055519 316842104900876091801083279)
    ·
      refine ⟨475263157351314137701624919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316842104900876091801083279 475263157351314137701624919)
      ·
        refine ⟨712894736026971206552437379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475263157351314137701624919 712894736026971206552437379)
        ·
          refine ⟨1069342104040456809828656069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712894736026971206552437379 1069342104040456809828656069)
          ·
            refine ⟨200501644507585651842873013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1069342104040456809828656069 200501644507585651842873013)
            ·
              refine ⟨18797029172586154860269345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200501644507585651842873013 18797029172586154860269345)
              ·
                refine ⟨14097771879439616145202009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18797029172586154860269345 14097771879439616145202009)
                ·
                  refine ⟨10573328909579712108901507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14097771879439616145202009 10573328909579712108901507)
                  ·
                    refine ⟨15859993364369568163352261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10573328909579712108901507 15859993364369568163352261)
                    ·
                      refine ⟨2973748755819294030628549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15859993364369568163352261 2973748755819294030628549)
                      ·
                        rfl

theorem cell23_5791355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4].length) (baseStart_5791355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791355 prefixEnd_5791355 := by exact prefixLift 5791355
  have htrace : WordTrace (prefixWord ++ tailWord_5791355) baseStart_5791355 baseEnd_5791355 := by
    simpa [prefixWord, tailWord_5791355, baseEnd_5791355] using wordTrace_append hprefix tailTrace_5791355
  have hstable : (prefixWord ++ tailWord_5791355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791355).length < 2 ^ (prefixWord ++ tailWord_5791355).sum := by decide
  have hdescent : baseEnd_5791355 < baseStart_5791355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791392 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_5791392 : Nat := 118140960795 + 5791392 * 2 ^ 59
def prefixEnd_5791392 : Nat := 4983230072969 + 3 ^ 40 * 5791392 * 2
def baseEnd_5791392 : Nat := 2973767754603510385865879

theorem tailTrace_5791392 : CollatzResearch.WordTrace tailWord_5791392 prefixEnd_5791392 2973767754603510385865879 := by
  unfold tailWord_5791392
  simp only [CollatzResearch.WordTrace]
  refine ⟨105614709717391674926576215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140819612956522233235434953 105614709717391674926576215)
  ·
    refine ⟨158422064576087512389864323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105614709717391674926576215 158422064576087512389864323)
    ·
      refine ⟨237633096864131268584796485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158422064576087512389864323 237633096864131268584796485)
      ·
        refine ⟨44556205662024612859649341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237633096864131268584796485 44556205662024612859649341)
        ·
          refine ⟨16708577123259229822368503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44556205662024612859649341 16708577123259229822368503)
          ·
            refine ⟨25062865684888844733552755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16708577123259229822368503 25062865684888844733552755)
            ·
              refine ⟨37594298527333267100329133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25062865684888844733552755 37594298527333267100329133)
              ·
                refine ⟨14097861947749975162623425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37594298527333267100329133 14097861947749975162623425)
                ·
                  refine ⟨10573396460812481371967569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14097861947749975162623425 10573396460812481371967569)
                  ·
                    refine ⟨7930047345609361028975677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10573396460812481371967569 7930047345609361028975677)
                    ·
                      refine ⟨2973767754603510385865879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7930047345609361028975677 2973767754603510385865879)
                      ·
                        rfl

theorem cell23_5791392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_5791392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791392 prefixEnd_5791392 := by exact prefixLift 5791392
  have htrace : WordTrace (prefixWord ++ tailWord_5791392) baseStart_5791392 baseEnd_5791392 := by
    simpa [prefixWord, tailWord_5791392, baseEnd_5791392] using wordTrace_append hprefix tailTrace_5791392
  have hstable : (prefixWord ++ tailWord_5791392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791392).length < 2 ^ (prefixWord ++ tailWord_5791392).sum := by decide
  have hdescent : baseEnd_5791392 < baseStart_5791392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791432 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_5791432 : Nat := 118140960795 + 5791432 * 2 ^ 59
def prefixEnd_5791432 : Nat := 4983230072969 + 3 ^ 40 * 5791432 * 2
def baseEnd_5791432 : Nat := 2973788293829690229365695

theorem tailTrace_5791432 : CollatzResearch.WordTrace tailWord_5791432 prefixEnd_5791432 2973788293829690229365695 := by
  unfold tailWord_5791432
  simp only [CollatzResearch.WordTrace]
  refine ⟨105615439177319218342304275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140820585569758957789739033 105615439177319218342304275)
  ·
    refine ⟨158423158765978827513456413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105615439177319218342304275 158423158765978827513456413)
    ·
      refine ⟨59408684537242060317546155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158423158765978827513456413 59408684537242060317546155)
      ·
        refine ⟨89113026805863090476319233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59408684537242060317546155 89113026805863090476319233)
        ·
          refine ⟨66834770104397317857239425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89113026805863090476319233 66834770104397317857239425)
          ·
            refine ⟨50126077578297988392929569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66834770104397317857239425 50126077578297988392929569)
            ·
              refine ⟨37594558183723491294697177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50126077578297988392929569 37594558183723491294697177)
              ·
                refine ⟨28195918637792618471022883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37594558183723491294697177 28195918637792618471022883)
                ·
                  refine ⟨42293877956688927706534325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28195918637792618471022883 42293877956688927706534325)
                  ·
                    refine ⟨3965051058439586972487593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42293877956688927706534325 3965051058439586972487593)
                    ·
                      refine ⟨2973788293829690229365695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965051058439586972487593 2973788293829690229365695)
                      ·
                        rfl

theorem cell23_5791432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_5791432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791432 prefixEnd_5791432 := by exact prefixLift 5791432
  have htrace : WordTrace (prefixWord ++ tailWord_5791432) baseStart_5791432 baseEnd_5791432 := by
    simpa [prefixWord, tailWord_5791432, baseEnd_5791432] using wordTrace_append hprefix tailTrace_5791432
  have hstable : (prefixWord ++ tailWord_5791432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791432).length < 2 ^ (prefixWord ++ tailWord_5791432).sum := by decide
  have hdescent : baseEnd_5791432 < baseStart_5791432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791442 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_5791442 : Nat := 118140960795 + 5791442 * 2 ^ 59
def prefixEnd_5791442 : Nat := 4983230072969 + 3 ^ 40 * 5791442 * 2
def baseEnd_5791442 : Nat := 991264476212078396746883

theorem tailTrace_5791442 : CollatzResearch.WordTrace tailWord_5791442 prefixEnd_5791442 991264476212078396746883 := by
  unfold tailWord_5791442
  simp only [CollatzResearch.WordTrace]
  refine ⟨52807810771150552098118145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140820828723068138928315053 52807810771150552098118145)
  ·
    refine ⟨39605858078362914073588609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52807810771150552098118145 39605858078362914073588609)
    ·
      refine ⟨29704393558772185555191457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39605858078362914073588609 29704393558772185555191457)
      ·
        refine ⟨22278295169079139166393593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29704393558772185555191457 22278295169079139166393593)
        ·
          refine ⟨16708721376809354374795195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22278295169079139166393593 16708721376809354374795195)
          ·
            refine ⟨25063082065214031562192793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16708721376809354374795195 25063082065214031562192793)
            ·
              refine ⟨18797311548910523671644595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25063082065214031562192793 18797311548910523671644595)
              ·
                refine ⟨28195967323365785507466893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18797311548910523671644595 28195967323365785507466893)
                ·
                  refine ⟨10573487746262169565300085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28195967323365785507466893 10573487746262169565300085)
                  ·
                    refine ⟨991264476212078396746883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10573487746262169565300085 991264476212078396746883)
                    ·
                      rfl

theorem cell23_5791442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_5791442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791442 prefixEnd_5791442 := by exact prefixLift 5791442
  have htrace : WordTrace (prefixWord ++ tailWord_5791442) baseStart_5791442 baseEnd_5791442 := by
    simpa [prefixWord, tailWord_5791442, baseEnd_5791442] using wordTrace_append hprefix tailTrace_5791442
  have hstable : (prefixWord ++ tailWord_5791442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791442).length < 2 ^ (prefixWord ++ tailWord_5791442).sum := by decide
  have hdescent : baseEnd_5791442 < baseStart_5791442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791449 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 2, 3, 2]
def baseStart_5791449 : Nat := 118140960795 + 5791449 * 2 ^ 59
def prefixEnd_5791449 : Nat := 4983230072969 + 3 ^ 40 * 5791449 * 2
def baseEnd_5791449 : Nat := 2973797023000816662853117

theorem tailTrace_5791449 : CollatzResearch.WordTrace tailWord_5791449 prefixEnd_5791449 2973797023000816662853117 := by
  unfold tailWord_5791449
  simp only [CollatzResearch.WordTrace]
  refine ⟨211231498395576848587977401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140820998930384565725318267 211231498395576848587977401)
  ·
    refine ⟨158423623796682636440983051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211231498395576848587977401 158423623796682636440983051)
    ·
      refine ⟨237635435695023954661474577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158423623796682636440983051 237635435695023954661474577)
      ·
        refine ⟨178226576771267965996105933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237635435695023954661474577 178226576771267965996105933)
        ·
          refine ⟨66834966289225487248539725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178226576771267965996105933 66834966289225487248539725)
          ·
            refine ⟨25063112358459557718202397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66834966289225487248539725 25063112358459557718202397)
            ·
              refine ⟨9398667134422334144325899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25063112358459557718202397 9398667134422334144325899)
              ·
                refine ⟨14098000701633501216488849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9398667134422334144325899 14098000701633501216488849)
                ·
                  refine ⟨10573500526225125912366637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14098000701633501216488849 10573500526225125912366637)
                  ·
                    refine ⟨3965062697334422217137489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10573500526225125912366637 3965062697334422217137489)
                    ·
                      refine ⟨2973797023000816662853117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965062697334422217137489 2973797023000816662853117)
                      ·
                        rfl

theorem cell23_5791449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_5791449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791449 prefixEnd_5791449 := by exact prefixLift 5791449
  have htrace : WordTrace (prefixWord ++ tailWord_5791449) baseStart_5791449 baseEnd_5791449 := by
    simpa [prefixWord, tailWord_5791449, baseEnd_5791449] using wordTrace_append hprefix tailTrace_5791449
  have hstable : (prefixWord ++ tailWord_5791449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791449).length < 2 ^ (prefixWord ++ tailWord_5791449).sum := by decide
  have hdescent : baseEnd_5791449 < baseStart_5791449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791455 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 1, 6]
def baseStart_5791455 : Nat := 118140960795 + 5791455 * 2 ^ 59
def prefixEnd_5791455 : Nat := 4983230072969 + 3 ^ 40 * 5791455 * 2
def baseEnd_5791455 : Nat := 991266701294914546459363

theorem tailTrace_5791455 : CollatzResearch.WordTrace tailWord_5791455 prefixEnd_5791455 991266701294914546459363 := by
  unfold tailWord_5791455
  simp only [CollatzResearch.WordTrace]
  refine ⟨211231717233555111612695819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140821144822370074408463879 211231717233555111612695819)
  ·
    refine ⟨316847575850332667419043729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211231717233555111612695819 316847575850332667419043729)
    ·
      refine ⟨237635681887749500564282797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316847575850332667419043729 237635681887749500564282797)
      ·
        refine ⟨89113380707906062711606049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237635681887749500564282797 89113380707906062711606049)
        ·
          refine ⟨66835035530929547033704537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89113380707906062711606049 66835035530929547033704537)
          ·
            refine ⟨50126276648197160275278403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66835035530929547033704537 50126276648197160275278403)
            ·
              refine ⟨75189414972295740412917605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50126276648197160275278403 75189414972295740412917605)
              ·
                refine ⟨14098015307305451327422051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75189414972295740412917605 14098015307305451327422051)
                ·
                  refine ⟨21147022960958176991133077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14098015307305451327422051 21147022960958176991133077)
                  ·
                    refine ⟨991266701294914546459363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21147022960958176991133077 991266701294914546459363)
                    ·
                      rfl

theorem cell23_5791455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_5791455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791455 prefixEnd_5791455 := by exact prefixLift 5791455
  have htrace : WordTrace (prefixWord ++ tailWord_5791455) baseStart_5791455 baseEnd_5791455 := by
    simpa [prefixWord, tailWord_5791455, baseEnd_5791455] using wordTrace_append hprefix tailTrace_5791455
  have hstable : (prefixWord ++ tailWord_5791455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791455).length < 2 ^ (prefixWord ++ tailWord_5791455).sum := by decide
  have hdescent : baseEnd_5791455 < baseStart_5791455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791459 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 1, 5]
def baseStart_5791459 : Nat := 118140960795 + 5791459 * 2 ^ 59
def prefixEnd_5791459 : Nat := 4983230072969 + 3 ^ 40 * 5791459 * 2
def baseEnd_5791459 : Nat := 991267385935787207909357

theorem tailTrace_5791459 : CollatzResearch.WordTrace tailWord_5791459 prefixEnd_5791459 991267385935787207909357 := by
  unfold tailWord_5791459
  simp only [CollatzResearch.WordTrace]
  refine ⟨211231863125540620295841431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140821242083693746863894287 211231863125540620295841431)
  ·
    refine ⟨316847794688310930443762147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211231863125540620295841431 316847794688310930443762147)
    ·
      refine ⟨475271692032466395665643221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316847794688310930443762147 475271692032466395665643221)
      ·
        refine ⟨11139180282010931148413513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 475271692032466395665643221 11139180282010931148413513)
        ·
          refine ⟨8354385211508198361310135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11139180282010931148413513 8354385211508198361310135)
          ·
            refine ⟨12531577817262297541965203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8354385211508198361310135 12531577817262297541965203)
            ·
              refine ⟨18797366725893446312947805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12531577817262297541965203 18797366725893446312947805)
              ·
                refine ⟨7049012522210042367355427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18797366725893446312947805 7049012522210042367355427)
                ·
                  refine ⟨10573518783315063551033141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049012522210042367355427 10573518783315063551033141)
                  ·
                    refine ⟨991267385935787207909357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10573518783315063551033141 991267385935787207909357)
                    ·
                      rfl

theorem cell23_5791459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 5].length) (baseStart_5791459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791459 prefixEnd_5791459 := by exact prefixLift 5791459
  have htrace : WordTrace (prefixWord ++ tailWord_5791459) baseStart_5791459 baseEnd_5791459 := by
    simpa [prefixWord, tailWord_5791459, baseEnd_5791459] using wordTrace_append hprefix tailTrace_5791459
  have hstable : (prefixWord ++ tailWord_5791459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791459).length < 2 ^ (prefixWord ++ tailWord_5791459).sum := by decide
  have hdescent : baseEnd_5791459 < baseStart_5791459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791465 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_5791465 : Nat := 118140960795 + 5791465 * 2 ^ 59
def prefixEnd_5791465 : Nat := 4983230072969 + 3 ^ 40 * 5791465 * 2
def baseEnd_5791465 : Nat := 2973805238691288600253043

theorem tailTrace_5791465 : CollatzResearch.WordTrace tailWord_5791465 prefixEnd_5791465 2973805238691288600253043 := by
  unfold tailWord_5791465
  simp only [CollatzResearch.WordTrace]
  refine ⟨211232081963518883320559849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140821387975679255547039899 211232081963518883320559849)
  ·
    refine ⟨158424061472639162490419887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211232081963518883320559849 158424061472639162490419887)
    ·
      refine ⟨237636092208958743735629831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158424061472639162490419887 237636092208958743735629831)
      ·
        refine ⟨356454138313438115603444747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237636092208958743735629831 356454138313438115603444747)
        ·
          refine ⟨534681207470157173405167121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356454138313438115603444747 534681207470157173405167121)
          ·
            refine ⟨401010905602617880053875341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534681207470157173405167121 401010905602617880053875341)
            ·
              refine ⟨150379089600981705020203253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401010905602617880053875341 150379089600981705020203253)
              ·
                refine ⟨14098039650092034845644055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150379089600981705020203253 14098039650092034845644055)
                ·
                  refine ⟨21147059475138052268466083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14098039650092034845644055 21147059475138052268466083)
                  ·
                    refine ⟨31720589212707078402699125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21147059475138052268466083 31720589212707078402699125)
                    ·
                      refine ⟨2973805238691288600253043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31720589212707078402699125 2973805238691288600253043)
                      ·
                        rfl

theorem cell23_5791465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_5791465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791465 prefixEnd_5791465 := by exact prefixLift 5791465
  have htrace : WordTrace (prefixWord ++ tailWord_5791465) baseStart_5791465 baseEnd_5791465 := by
    simpa [prefixWord, tailWord_5791465, baseEnd_5791465] using wordTrace_append hprefix tailTrace_5791465
  have hstable : (prefixWord ++ tailWord_5791465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791465).length < 2 ^ (prefixWord ++ tailWord_5791465).sum := by decide
  have hdescent : baseEnd_5791465 < baseStart_5791465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791472 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_5791472 : Nat := 118140960795 + 5791472 * 2 ^ 59
def prefixEnd_5791472 : Nat := 4983230072969 + 3 ^ 40 * 5791472 * 2
def baseEnd_5791472 : Nat := 991269611018623357621837

theorem tailTrace_5791472 : CollatzResearch.WordTrace tailWord_5791472 prefixEnd_5791472 991269611018623357621837 := by
  unfold tailWord_5791472
  simp only [CollatzResearch.WordTrace]
  refine ⟨105616168637246761758032335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140821558182995682344043113 105616168637246761758032335)
  ·
    refine ⟨158424252955870142637048503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105616168637246761758032335 158424252955870142637048503)
    ·
      refine ⟨237636379433805213955572755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158424252955870142637048503 237636379433805213955572755)
      ·
        refine ⟨356454569150707820933359133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237636379433805213955572755 356454569150707820933359133)
        ·
          refine ⟨133670463431515432850009675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356454569150707820933359133 133670463431515432850009675)
          ·
            refine ⟨200505695147273149275014513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133670463431515432850009675 200505695147273149275014513)
            ·
              refine ⟨150379271360454861956260885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200505695147273149275014513 150379271360454861956260885)
              ·
                refine ⟨7049028345021321654199729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150379271360454861956260885 7049028345021321654199729)
                ·
                  refine ⟨5286771258765991240649797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7049028345021321654199729 5286771258765991240649797)
                  ·
                    refine ⟨991269611018623357621837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286771258765991240649797 991269611018623357621837)
                    ·
                      rfl

theorem cell23_5791472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_5791472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791472 prefixEnd_5791472 := by exact prefixLift 5791472
  have htrace : WordTrace (prefixWord ++ tailWord_5791472) baseStart_5791472 baseEnd_5791472 := by
    simpa [prefixWord, tailWord_5791472, baseEnd_5791472] using wordTrace_append hprefix tailTrace_5791472
  have hstable : (prefixWord ++ tailWord_5791472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791472).length < 2 ^ (prefixWord ++ tailWord_5791472).sum := by decide
  have hdescent : baseEnd_5791472 < baseStart_5791472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791475 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_5791475 : Nat := 118140960795 + 5791475 * 2 ^ 59
def prefixEnd_5791475 : Nat := 4983230072969 + 3 ^ 40 * 5791475 * 2
def baseEnd_5791475 : Nat := 2973810373497833561127997

theorem tailTrace_5791475 : CollatzResearch.WordTrace tailWord_5791475 prefixEnd_5791475 2973810373497833561127997 := by
  unfold tailWord_5791475
  simp only [CollatzResearch.WordTrace]
  refine ⟨211232446693482655028423879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140821631128988436685615919 211232446693482655028423879)
  ·
    refine ⟨316848670040223982542635819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211232446693482655028423879 316848670040223982542635819)
    ·
      refine ⟨475273005060335973813953729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316848670040223982542635819 475273005060335973813953729)
      ·
        refine ⟨356454753795251980360465297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475273005060335973813953729 356454753795251980360465297)
        ·
          refine ⟨267341065346438985270348973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356454753795251980360465297 267341065346438985270348973)
          ·
            refine ⟨100252899504914619476380865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267341065346438985270348973 100252899504914619476380865)
            ·
              refine ⟨75189674628685964607285649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100252899504914619476380865 75189674628685964607285649)
              ·
                refine ⟨56392255971514473455464237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75189674628685964607285649 56392255971514473455464237)
                ·
                  refine ⟨21147095989317927545799089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56392255971514473455464237 21147095989317927545799089)
                  ·
                    refine ⟨15860321991988445659349317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21147095989317927545799089 15860321991988445659349317)
                    ·
                      refine ⟨2973810373497833561127997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15860321991988445659349317 2973810373497833561127997)
                      ·
                        rfl

theorem cell23_5791475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_5791475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791475 prefixEnd_5791475 := by exact prefixLift 5791475
  have htrace : WordTrace (prefixWord ++ tailWord_5791475) baseStart_5791475 baseEnd_5791475 := by
    simpa [prefixWord, tailWord_5791475, baseEnd_5791475] using wordTrace_append hprefix tailTrace_5791475
  have hstable : (prefixWord ++ tailWord_5791475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791475).length < 2 ^ (prefixWord ++ tailWord_5791475).sum := by decide
  have hdescent : baseEnd_5791475 < baseStart_5791475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791479 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_5791479 : Nat := 118140960795 + 5791479 * 2 ^ 59
def prefixEnd_5791479 : Nat := 4983230072969 + 3 ^ 40 * 5791479 * 2
def baseEnd_5791479 : Nat := 2973812427420451545477979

theorem tailTrace_5791479 : CollatzResearch.WordTrace tailWord_5791479 prefixEnd_5791479 2973812427420451545477979 := by
  unfold tailWord_5791479
  simp only [CollatzResearch.WordTrace]
  refine ⟨211232592585468163711569491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140821728390312109141046327 211232592585468163711569491)
  ·
    refine ⟨316848888878202245567354237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211232592585468163711569491 316848888878202245567354237)
    ·
      refine ⟨118818333329325842087757839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316848888878202245567354237 118818333329325842087757839)
      ·
        refine ⟨178227499993988763131636759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118818333329325842087757839 178227499993988763131636759)
        ·
          refine ⟨267341249990983144697455139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178227499993988763131636759 267341249990983144697455139)
          ·
            refine ⟨401011874986474717046182709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267341249990983144697455139 401011874986474717046182709)
            ·
              refine ⟨37594863279982004723079629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401011874986474717046182709 37594863279982004723079629)
              ·
                refine ⟨14098073729993251771154861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37594863279982004723079629 14098073729993251771154861)
                ·
                  refine ⟨5286777648747469414183073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14098073729993251771154861 5286777648747469414183073)
                  ·
                    refine ⟨3965083236560602060637305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286777648747469414183073 3965083236560602060637305)
                    ·
                      refine ⟨2973812427420451545477979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965083236560602060637305 2973812427420451545477979)
                      ·
                        rfl

theorem cell23_5791479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_5791479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791479 prefixEnd_5791479 := by exact prefixLift 5791479
  have htrace : WordTrace (prefixWord ++ tailWord_5791479) baseStart_5791479 baseEnd_5791479 := by
    simpa [prefixWord, tailWord_5791479, baseEnd_5791479] using wordTrace_append hprefix tailTrace_5791479
  have hstable : (prefixWord ++ tailWord_5791479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791479).length < 2 ^ (prefixWord ++ tailWord_5791479).sum := by decide
  have hdescent : baseEnd_5791479 < baseStart_5791479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791492 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5791492 : Nat := 118140960795 + 5791492 * 2 ^ 59
def prefixEnd_5791492 : Nat := 4983230072969 + 3 ^ 40 * 5791492 * 2
def baseEnd_5791492 : Nat := 2973819102668959994615419

theorem tailTrace_5791492 : CollatzResearch.WordTrace tailWord_5791492 prefixEnd_5791492 2973819102668959994615419 := by
  unfold tailWord_5791492
  simp only [CollatzResearch.WordTrace]
  refine ⟨105616533367210533465896365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140822044489614044621195153 105616533367210533465896365)
  ·
    refine ⟨39606200012703950049711137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105616533367210533465896365 39606200012703950049711137)
    ·
      refine ⟨29704650009527962537283353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39606200012703950049711137 29704650009527962537283353)
      ·
        refine ⟨22278487507145971902962515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29704650009527962537283353 22278487507145971902962515)
        ·
          refine ⟨33417731260718957854443773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22278487507145971902962515 33417731260718957854443773)
          ·
            refine ⟨12531649222769609195416415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33417731260718957854443773 12531649222769609195416415)
            ·
              refine ⟨18797473834154413793124623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12531649222769609195416415 18797473834154413793124623)
              ·
                refine ⟨28196210751231620689686935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18797473834154413793124623 28196210751231620689686935)
                ·
                  refine ⟨42294316126847431034530403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28196210751231620689686935 42294316126847431034530403)
                  ·
                    refine ⟨63441474190271146551795605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42294316126847431034530403 63441474190271146551795605)
                    ·
                      refine ⟨2973819102668959994615419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63441474190271146551795605 2973819102668959994615419)
                      ·
                        rfl

theorem cell23_5791492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5791492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791492 prefixEnd_5791492 := by exact prefixLift 5791492
  have htrace : WordTrace (prefixWord ++ tailWord_5791492) baseStart_5791492 baseEnd_5791492 := by
    simpa [prefixWord, tailWord_5791492, baseEnd_5791492] using wordTrace_append hprefix tailTrace_5791492
  have hstable : (prefixWord ++ tailWord_5791492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791492).length < 2 ^ (prefixWord ++ tailWord_5791492).sum := by decide
  have hdescent : baseEnd_5791492 < baseStart_5791492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791502 : List Nat := [4, 1, 1, 2, 1, 1, 6, 7]
def baseStart_5791502 : Nat := 118140960795 + 5791502 * 2 ^ 59
def prefixEnd_5791502 : Nat := 4983230072969 + 3 ^ 40 * 5791502 * 2
def baseEnd_5791502 : Nat := 110141638425018702055199

theorem tailTrace_5791502 : CollatzResearch.WordTrace tailWord_5791502 prefixEnd_5791502 110141638425018702055199 := by
  unfold tailWord_5791502
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404178933048104829957095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140822287642923225759771173 26404178933048104829957095)
  ·
    refine ⟨39606268399572157244935643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26404178933048104829957095 39606268399572157244935643)
    ·
      refine ⟨59409402599358235867403465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39606268399572157244935643 59409402599358235867403465)
      ·
        refine ⟨44557051949518676900552599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59409402599358235867403465 44557051949518676900552599)
        ·
          refine ⟨66835577924278015350828899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44557051949518676900552599 66835577924278015350828899)
          ·
            refine ⟨100253366886417023026243349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66835577924278015350828899 100253366886417023026243349)
            ·
              refine ⟨4699376572800797954355157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100253366886417023026243349 4699376572800797954355157)
              ·
                refine ⟨110141638425018702055199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4699376572800797954355157 110141638425018702055199)
                ·
                  rfl

theorem cell23_5791502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_5791502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791502 prefixEnd_5791502 := by exact prefixLift 5791502
  have htrace : WordTrace (prefixWord ++ tailWord_5791502) baseStart_5791502 baseEnd_5791502 := by
    simpa [prefixWord, tailWord_5791502, baseEnd_5791502] using wordTrace_append hprefix tailTrace_5791502
  have hstable : (prefixWord ++ tailWord_5791502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791502).length < 2 ^ (prefixWord ++ tailWord_5791502).sum := by decide
  have hdescent : baseEnd_5791502 < baseStart_5791502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791512 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_5791512 : Nat := 118140960795 + 5791512 * 2 ^ 59
def prefixEnd_5791512 : Nat := 4983230072969 + 3 ^ 40 * 5791512 * 2
def baseEnd_5791512 : Nat := 2973829372282049916365327

theorem tailTrace_5791512 : CollatzResearch.WordTrace tailWord_5791512 prefixEnd_5791512 2973829372282049916365327 := by
  unfold tailWord_5791512
  simp only [CollatzResearch.WordTrace]
  refine ⟨105616898097174305173760395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140822530796232406898347193 105616898097174305173760395)
  ·
    refine ⟨158425347145761457760640593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105616898097174305173760395 158425347145761457760640593)
    ·
      refine ⟨118819010359321093320480445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158425347145761457760640593 118819010359321093320480445)
      ·
        refine ⟨44557128884745409995180167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118819010359321093320480445 44557128884745409995180167)
        ·
          refine ⟨66835693327118114992770251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44557128884745409995180167 66835693327118114992770251)
          ·
            refine ⟨100253539990677172489155377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66835693327118114992770251 100253539990677172489155377)
            ·
              refine ⟨75190154993007879366866533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100253539990677172489155377 75190154993007879366866533)
              ·
                refine ⟨14098154061188977381287475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75190154993007879366866533 14098154061188977381287475)
                ·
                  refine ⟨21147231091783466071931213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14098154061188977381287475 21147231091783466071931213)
                  ·
                    refine ⟨7930211659418799776974205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21147231091783466071931213 7930211659418799776974205)
                    ·
                      refine ⟨2973829372282049916365327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7930211659418799776974205 2973829372282049916365327)
                      ·
                        rfl

theorem cell23_5791512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_5791512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791512 prefixEnd_5791512 := by exact prefixLift 5791512
  have htrace : WordTrace (prefixWord ++ tailWord_5791512) baseStart_5791512 baseEnd_5791512 := by
    simpa [prefixWord, tailWord_5791512, baseEnd_5791512] using wordTrace_append hprefix tailTrace_5791512
  have hstable : (prefixWord ++ tailWord_5791512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791512).length < 2 ^ (prefixWord ++ tailWord_5791512).sum := by decide
  have hdescent : baseEnd_5791512 < baseStart_5791512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791535 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_5791535 : Nat := 118140960795 + 5791535 * 2 ^ 59
def prefixEnd_5791535 : Nat := 4983230072969 + 3 ^ 40 * 5791535 * 2
def baseEnd_5791535 : Nat := 2973841182337103326377721

theorem tailTrace_5791535 : CollatzResearch.WordTrace tailWord_5791535 prefixEnd_5791535 2973841182337103326377721 := by
  unfold tailWord_5791535
  simp only [CollatzResearch.WordTrace]
  refine ⟨211234635073265285275608059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140823090048843523517072039 211234635073265285275608059)
  ·
    refine ⟨316851952609897927913412089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211234635073265285275608059 316851952609897927913412089)
    ·
      refine ⟨237638964457423445935059067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316851952609897927913412089 237638964457423445935059067)
      ·
        refine ⟨356458446686135168902588601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237638964457423445935059067 356458446686135168902588601)
        ·
          refine ⟨267343835014601376676941451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356458446686135168902588601 267343835014601376676941451)
          ·
            refine ⟨401015752521902065015412177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267343835014601376676941451 401015752521902065015412177)
            ·
              refine ⟨300761814391426548761559133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401015752521902065015412177 300761814391426548761559133)
              ·
                refine ⟨112785680396784955785584675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300761814391426548761559133 112785680396784955785584675)
                ·
                  refine ⟨169178520595177433678377013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112785680396784955785584675 169178520595177433678377013)
                  ·
                    refine ⟨15860486305797884407347845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169178520595177433678377013 15860486305797884407347845)
                    ·
                      refine ⟨2973841182337103326377721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15860486305797884407347845 2973841182337103326377721)
                      ·
                        rfl

theorem cell23_5791535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_5791535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791535 prefixEnd_5791535 := by exact prefixLift 5791535
  have htrace : WordTrace (prefixWord ++ tailWord_5791535) baseStart_5791535 baseEnd_5791535 := by
    simpa [prefixWord, tailWord_5791535, baseEnd_5791535] using wordTrace_append hprefix tailTrace_5791535
  have hstable : (prefixWord ++ tailWord_5791535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791535).length < 2 ^ (prefixWord ++ tailWord_5791535).sum := by decide
  have hdescent : baseEnd_5791535 < baseStart_5791535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791546 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_5791546 : Nat := 118140960795 + 5791546 * 2 ^ 59
def prefixEnd_5791546 : Nat := 4983230072969 + 3 ^ 40 * 5791546 * 2
def baseEnd_5791546 : Nat := 2973846830624302783340171

theorem tailTrace_5791546 : CollatzResearch.WordTrace tailWord_5791546 prefixEnd_5791546 2973846830624302783340171 := by
  unfold tailWord_5791546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52808759069056358538564623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140823357517483622769505661 52808759069056358538564623)
  ·
    refine ⟨79213138603584537807846935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52808759069056358538564623 79213138603584537807846935)
    ·
      refine ⟨118819707905376806711770403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79213138603584537807846935 118819707905376806711770403)
      ·
        refine ⟨178229561858065210067655605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118819707905376806711770403 178229561858065210067655605)
        ·
          refine ⟨16709021424193613443842713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178229561858065210067655605 16709021424193613443842713)
          ·
            refine ⟨12531766068145210082882035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16709021424193613443842713 12531766068145210082882035)
            ·
              refine ⟨18797649102217815124323053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12531766068145210082882035 18797649102217815124323053)
              ·
                refine ⟨7049118413331680671621145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18797649102217815124323053 7049118413331680671621145)
                ·
                  refine ⟨5286838809998760503715859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7049118413331680671621145 5286838809998760503715859)
                  ·
                    refine ⟨7930258214998140755573789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286838809998760503715859 7930258214998140755573789)
                    ·
                      refine ⟨2973846830624302783340171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7930258214998140755573789 2973846830624302783340171)
                      ·
                        rfl

theorem cell23_5791546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_5791546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791546 prefixEnd_5791546 := by exact prefixLift 5791546
  have htrace : WordTrace (prefixWord ++ tailWord_5791546) baseStart_5791546 baseEnd_5791546 := by
    simpa [prefixWord, tailWord_5791546, baseEnd_5791546] using wordTrace_append hprefix tailTrace_5791546
  have hstable : (prefixWord ++ tailWord_5791546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791546).length < 2 ^ (prefixWord ++ tailWord_5791546).sum := by decide
  have hdescent : baseEnd_5791546 < baseStart_5791546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791569 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_5791569 : Nat := 118140960795 + 5791569 * 2 ^ 59
def prefixEnd_5791569 : Nat := 4983230072969 + 3 ^ 40 * 5791569 * 2
def baseEnd_5791569 : Nat := 2973858640679356193352565

theorem tailTrace_5791569 : CollatzResearch.WordTrace tailWord_5791569 prefixEnd_5791569 2973858640679356193352565 := by
  unfold tailWord_5791569
  simp only [CollatzResearch.WordTrace]
  refine ⟨211235875155142109082345761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140823916770094739388230507 211235875155142109082345761)
  ·
    refine ⟨158426906366356581811759321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211235875155142109082345761 158426906366356581811759321)
    ·
      refine ⟨118820179774767436358819491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158426906366356581811759321 118820179774767436358819491)
      ·
        refine ⟨178230269662151154538229237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118820179774767436358819491 178230269662151154538229237)
        ·
          refine ⟨16709087780826670737958991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178230269662151154538229237 16709087780826670737958991)
          ·
            refine ⟨25063631671240006106938487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16709087780826670737958991 25063631671240006106938487)
            ·
              refine ⟨37595447506860009160407731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25063631671240006106938487 37595447506860009160407731)
              ·
                refine ⟨56393171260290013740611597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37595447506860009160407731 56393171260290013740611597)
                ·
                  refine ⟨21147439222608755152729349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56393171260290013740611597 21147439222608755152729349)
                  ·
                    refine ⟨3965144854239141591136753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21147439222608755152729349 3965144854239141591136753)
                    ·
                      refine ⟨2973858640679356193352565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965144854239141591136753 2973858640679356193352565)
                      ·
                        rfl

theorem cell23_5791569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_5791569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791569 prefixEnd_5791569 := by exact prefixLift 5791569
  have htrace : WordTrace (prefixWord ++ tailWord_5791569) baseStart_5791569 baseEnd_5791569 := by
    simpa [prefixWord, tailWord_5791569, baseEnd_5791569] using wordTrace_append hprefix tailTrace_5791569
  have hstable : (prefixWord ++ tailWord_5791569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791569).length < 2 ^ (prefixWord ++ tailWord_5791569).sum := by decide
  have hdescent : baseEnd_5791569 < baseStart_5791569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791573 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5791573 : Nat := 118140960795 + 5791573 * 2 ^ 59
def prefixEnd_5791573 : Nat := 4983230072969 + 3 ^ 40 * 5791573 * 2
def baseEnd_5791573 : Nat := 2973860694601974177702547

theorem tailTrace_5791573 : CollatzResearch.WordTrace tailWord_5791573 prefixEnd_5791573 2973860694601974177702547 := by
  unfold tailWord_5791573
  simp only [CollatzResearch.WordTrace]
  refine ⟨211236021047127617765491373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140824014031418411843660915 211236021047127617765491373)
  ·
    refine ⟨79213507892672856662059265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211236021047127617765491373 79213507892672856662059265)
    ·
      refine ⟨59410130919504642496544449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79213507892672856662059265 59410130919504642496544449)
      ·
        refine ⟨44557598189628481872408337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59410130919504642496544449 44557598189628481872408337)
        ·
          refine ⟨33418198642221361404306253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44557598189628481872408337 33418198642221361404306253)
          ·
            refine ⟨12531824490833010526614845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33418198642221361404306253 12531824490833010526614845)
            ·
              refine ⟨4699434184062378947480567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12531824490833010526614845 4699434184062378947480567)
              ·
                refine ⟨7049151276093568421220851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699434184062378947480567 7049151276093568421220851)
                ·
                  refine ⟨10573726914140352631831277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049151276093568421220851 10573726914140352631831277)
                  ·
                    refine ⟨3965147592802632236936729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10573726914140352631831277 3965147592802632236936729)
                    ·
                      refine ⟨2973860694601974177702547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965147592802632236936729 2973860694601974177702547)
                      ·
                        rfl

theorem cell23_5791573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5791573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791573 prefixEnd_5791573 := by exact prefixLift 5791573
  have htrace : WordTrace (prefixWord ++ tailWord_5791573) baseStart_5791573 baseEnd_5791573 := by
    simpa [prefixWord, tailWord_5791573, baseEnd_5791573] using wordTrace_append hprefix tailTrace_5791573
  have hstable : (prefixWord ++ tailWord_5791573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791573).length < 2 ^ (prefixWord ++ tailWord_5791573).sum := by decide
  have hdescent : baseEnd_5791573 < baseStart_5791573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791592 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 7]
def baseStart_5791592 : Nat := 118140960795 + 5791592 * 2 ^ 59
def prefixEnd_5791592 : Nat := 4983230072969 + 3 ^ 40 * 5791592 * 2
def baseEnd_5791592 : Nat := 330430050081601067040551

theorem tailTrace_5791592 : CollatzResearch.WordTrace tailWord_5791592 prefixEnd_5791592 330430050081601067040551 := by
  unfold tailWord_5791592
  simp only [CollatzResearch.WordTrace]
  refine ⟨105618357017029392005216515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140824476022705856006955353 105618357017029392005216515)
  ·
    refine ⟨158427535525544088007824773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105618357017029392005216515 158427535525544088007824773)
    ·
      refine ⟨29705162911039516501467145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158427535525544088007824773 29705162911039516501467145)
      ·
        refine ⟨22278872183279637376100359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29705162911039516501467145 22278872183279637376100359)
        ·
          refine ⟨33418308274919456064150539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22278872183279637376100359 33418308274919456064150539)
          ·
            refine ⟨50127462412379184096225809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33418308274919456064150539 50127462412379184096225809)
            ·
              refine ⟨37595596809284388072169357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50127462412379184096225809 37595596809284388072169357)
              ·
                refine ⟨14098348803481645527063509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37595596809284388072169357 14098348803481645527063509)
                ·
                  refine ⟨330430050081601067040551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14098348803481645527063509 330430050081601067040551)
                  ·
                    rfl

theorem cell23_5791592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_5791592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791592 prefixEnd_5791592 := by exact prefixLift 5791592
  have htrace : WordTrace (prefixWord ++ tailWord_5791592) baseStart_5791592 baseEnd_5791592 := by
    simpa [prefixWord, tailWord_5791592, baseEnd_5791592] using wordTrace_append hprefix tailTrace_5791592
  have hstable : (prefixWord ++ tailWord_5791592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791592).length < 2 ^ (prefixWord ++ tailWord_5791592).sum := by decide
  have hdescent : baseEnd_5791592 < baseStart_5791592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791595 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_5791595 : Nat := 118140960795 + 5791595 * 2 ^ 59
def prefixEnd_5791595 : Nat := 4983230072969 + 3 ^ 40 * 5791595 * 2
def baseEnd_5791595 : Nat := 2973871991176373091627445

theorem tailTrace_5791595 : CollatzResearch.WordTrace tailWord_5791595 prefixEnd_5791595 2973871991176373091627445 := by
  unfold tailWord_5791595
  simp only [CollatzResearch.WordTrace]
  refine ⟨211236823453047915522792239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140824548968698610348528159 211236823453047915522792239)
  ·
    refine ⟨316855235179571873284188359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211236823453047915522792239 316855235179571873284188359)
    ·
      refine ⟨475282852769357809926282539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316855235179571873284188359 475282852769357809926282539)
      ·
        refine ⟨712924279154036714889423809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475282852769357809926282539 712924279154036714889423809)
        ·
          refine ⟨534693209365527536167067857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712924279154036714889423809 534693209365527536167067857)
          ·
            refine ⟨401019907024145652125300893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534693209365527536167067857 401019907024145652125300893)
            ·
              refine ⟨150382465134054619546987835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401019907024145652125300893 150382465134054619546987835)
              ·
                refine ⟨225573697701081929320481753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150382465134054619546987835 225573697701081929320481753)
                ·
                  refine ⟨169180273275811446990361315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225573697701081929320481753 169180273275811446990361315)
                  ·
                    refine ⟨253770409913717170485541973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169180273275811446990361315 253770409913717170485541973)
                    ·
                      refine ⟨2973871991176373091627445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 253770409913717170485541973 2973871991176373091627445)
                      ·
                        rfl

theorem cell23_5791595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_5791595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791595 prefixEnd_5791595 := by exact prefixLift 5791595
  have htrace : WordTrace (prefixWord ++ tailWord_5791595) baseStart_5791595 baseEnd_5791595 := by
    simpa [prefixWord, tailWord_5791595, baseEnd_5791595] using wordTrace_append hprefix tailTrace_5791595
  have hstable : (prefixWord ++ tailWord_5791595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791595).length < 2 ^ (prefixWord ++ tailWord_5791595).sum := by decide
  have hdescent : baseEnd_5791595 < baseStart_5791595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791672 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_5791672 : Nat := 118140960795 + 5791672 * 2 ^ 59
def prefixEnd_5791672 : Nat := 4983230072969 + 3 ^ 40 * 5791672 * 2
def baseEnd_5791672 : Nat := 2973911529186769290364591

theorem tailTrace_5791672 : CollatzResearch.WordTrace tailWord_5791672 prefixEnd_5791672 2973911529186769290364591 := by
  unfold tailWord_5791672
  simp only [CollatzResearch.WordTrace]
  refine ⟨105619815936884478836672635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140826421249179305115563513 105619815936884478836672635)
  ·
    refine ⟨158429723905326718255008953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105619815936884478836672635 158429723905326718255008953)
    ·
      refine ⟨118822292928995038691256715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158429723905326718255008953 118822292928995038691256715)
      ·
        refine ⟨178233439393492558036885073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118822292928995038691256715 178233439393492558036885073)
        ·
          refine ⟨133675079545119418527663805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178233439393492558036885073 133675079545119418527663805)
          ·
            refine ⟨50128154829419781947873927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133675079545119418527663805 50128154829419781947873927)
            ·
              refine ⟨75192232244129672921810891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50128154829419781947873927 75192232244129672921810891)
              ·
                refine ⟨112788348366194509382716337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75192232244129672921810891 112788348366194509382716337)
                ·
                  refine ⟨84591261274645882037037253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112788348366194509382716337 84591261274645882037037253)
                  ·
                    refine ⟨15860861488996102881944485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84591261274645882037037253 15860861488996102881944485)
                    ·
                      refine ⟨2973911529186769290364591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15860861488996102881944485 2973911529186769290364591)
                      ·
                        rfl

theorem cell23_5791672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_5791672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791672 prefixEnd_5791672 := by exact prefixLift 5791672
  have htrace : WordTrace (prefixWord ++ tailWord_5791672) baseStart_5791672 baseEnd_5791672 := by
    simpa [prefixWord, tailWord_5791672, baseEnd_5791672] using wordTrace_append hprefix tailTrace_5791672
  have hstable : (prefixWord ++ tailWord_5791672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791672).length < 2 ^ (prefixWord ++ tailWord_5791672).sum := by decide
  have hdescent : baseEnd_5791672 < baseStart_5791672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791679 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_5791679 : Nat := 118140960795 + 5791679 * 2 ^ 59
def prefixEnd_5791679 : Nat := 4983230072969 + 3 ^ 40 * 5791679 * 2
def baseEnd_5791679 : Nat := 2973915123551350762977059

theorem tailTrace_5791679 : CollatzResearch.WordTrace tailWord_5791679 prefixEnd_5791679 2973915123551350762977059 := by
  unfold tailWord_5791679
  simp only [CollatzResearch.WordTrace]
  refine ⟨211239887184743597868850091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140826591456495731912566727 211239887184743597868850091)
  ·
    refine ⟨316859830777115396803275137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211239887184743597868850091 316859830777115396803275137)
    ·
      refine ⟨237644873082836547602456353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316859830777115396803275137 237644873082836547602456353)
      ·
        refine ⟨178233654812127410701842265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237644873082836547602456353 178233654812127410701842265)
        ·
          refine ⟨133675241109095558026381699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178233654812127410701842265 133675241109095558026381699)
          ·
            refine ⟨200512861663643337039572549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133675241109095558026381699 200512861663643337039572549)
            ·
              refine ⟨37596161561933125694919853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200512861663643337039572549 37596161561933125694919853)
              ·
                refine ⟨14098560585724922135594945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37596161561933125694919853 14098560585724922135594945)
                ·
                  refine ⟨10573920439293691601696209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14098560585724922135594945 10573920439293691601696209)
                  ·
                    refine ⟨7930440329470268701272157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10573920439293691601696209 7930440329470268701272157)
                    ·
                      refine ⟨2973915123551350762977059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7930440329470268701272157 2973915123551350762977059)
                      ·
                        rfl

theorem cell23_5791679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_5791679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791679 prefixEnd_5791679 := by exact prefixLift 5791679
  have htrace : WordTrace (prefixWord ++ tailWord_5791679) baseStart_5791679 baseEnd_5791679 := by
    simpa [prefixWord, tailWord_5791679, baseEnd_5791679] using wordTrace_append hprefix tailTrace_5791679
  have hstable : (prefixWord ++ tailWord_5791679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791679).length < 2 ^ (prefixWord ++ tailWord_5791679).sum := by decide
  have hdescent : baseEnd_5791679 < baseStart_5791679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791703 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 1, 4]
def baseStart_5791703 : Nat := 118140960795 + 5791703 * 2 ^ 59
def prefixEnd_5791703 : Nat := 4983230072969 + 3 ^ 40 * 5791703 * 2
def baseEnd_5791703 : Nat := 991309149029019556358983

theorem tailTrace_5791703 : CollatzResearch.WordTrace tailWord_5791703 prefixEnd_5791703 991309149029019556358983 := by
  unfold tailWord_5791703
  simp only [CollatzResearch.WordTrace]
  refine ⟨211240762536656649967723763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140827175024437766645149175 211240762536656649967723763)
  ·
    refine ⟨316861143804984974951585645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211240762536656649967723763 316861143804984974951585645)
    ·
      refine ⟨118822928926869365606844617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316861143804984974951585645 118822928926869365606844617)
      ·
        refine ⟨89117196695152024205133463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118822928926869365606844617 89117196695152024205133463)
        ·
          refine ⟨133675795042728036307700195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89117196695152024205133463 133675795042728036307700195)
          ·
            refine ⟨200513692564092054461550293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133675795042728036307700195 200513692564092054461550293)
            ·
              refine ⟨4699539669470907526442585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200513692564092054461550293 4699539669470907526442585)
              ·
                refine ⟨3524654752103180644831939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699539669470907526442585 3524654752103180644831939)
                ·
                  refine ⟨5286982128154770967247909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524654752103180644831939 5286982128154770967247909)
                  ·
                    refine ⟨991309149029019556358983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5286982128154770967247909 991309149029019556358983)
                    ·
                      rfl

theorem cell23_5791703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_5791703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791703 prefixEnd_5791703 := by exact prefixLift 5791703
  have htrace : WordTrace (prefixWord ++ tailWord_5791703) baseStart_5791703 baseEnd_5791703 := by
    simpa [prefixWord, tailWord_5791703, baseEnd_5791703] using wordTrace_append hprefix tailTrace_5791703
  have hstable : (prefixWord ++ tailWord_5791703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791703).length < 2 ^ (prefixWord ++ tailWord_5791703).sum := by decide
  have hdescent : baseEnd_5791703 < baseStart_5791703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791736 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_5791736 : Nat := 118140960795 + 5791736 * 2 ^ 59
def prefixEnd_5791736 : Nat := 4983230072969 + 3 ^ 40 * 5791736 * 2
def baseEnd_5791736 : Nat := 2973944391948657039964297

theorem tailTrace_5791736 : CollatzResearch.WordTrace tailWord_5791736 prefixEnd_5791736 2973944391948657039964297 := by
  unfold tailWord_5791736
  simp only [CollatzResearch.WordTrace]
  refine ⟨105620983072768548301837531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140827977430358064402450041 105620983072768548301837531)
  ·
    refine ⟨158431474609152822452756297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105620983072768548301837531 158431474609152822452756297)
    ·
      refine ⟨118823605956864616839567223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158431474609152822452756297 118823605956864616839567223)
      ·
        refine ⟨178235408935296925259350835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118823605956864616839567223 178235408935296925259350835)
        ·
          refine ⟨267353113402945387889026253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178235408935296925259350835 267353113402945387889026253)
          ·
            refine ⟨100257417526104520458384845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267353113402945387889026253 100257417526104520458384845)
            ·
              refine ⟨37596531572289195171894317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100257417526104520458384845 37596531572289195171894317)
              ·
                refine ⟨14098699339608448189460369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37596531572289195171894317 14098699339608448189460369)
                ·
                  refine ⟨10574024504706336142095277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14098699339608448189460369 10574024504706336142095277)
                  ·
                    refine ⟨3965259189264876053285729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10574024504706336142095277 3965259189264876053285729)
                    ·
                      refine ⟨2973944391948657039964297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965259189264876053285729 2973944391948657039964297)
                      ·
                        rfl

theorem cell23_5791736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_5791736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791736 prefixEnd_5791736 := by exact prefixLift 5791736
  have htrace : WordTrace (prefixWord ++ tailWord_5791736) baseStart_5791736 baseEnd_5791736 := by
    simpa [prefixWord, tailWord_5791736, baseEnd_5791736] using wordTrace_append hprefix tailTrace_5791736
  have hstable : (prefixWord ++ tailWord_5791736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791736).length < 2 ^ (prefixWord ++ tailWord_5791736).sum := by decide
  have hdescent : baseEnd_5791736 < baseStart_5791736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791800 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_5791800 : Nat := 118140960795 + 5791800 * 2 ^ 59
def prefixEnd_5791800 : Nat := 4983230072969 + 3 ^ 40 * 5791800 * 2
def baseEnd_5791800 : Nat := 2973977254710544789564003

theorem tailTrace_5791800 : CollatzResearch.WordTrace tailWord_5791800 prefixEnd_5791800 2973977254710544789564003 := by
  unfold tailWord_5791800
  simp only [CollatzResearch.WordTrace]
  refine ⟨105622150208652617767002427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140829533611536823689336569 105622150208652617767002427)
  ·
    refine ⟨158433225312978926650503641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105622150208652617767002427 158433225312978926650503641)
    ·
      refine ⟨118824918984734194987877731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158433225312978926650503641 118824918984734194987877731)
      ·
        refine ⟨178237378477101292481816597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118824918984734194987877731 178237378477101292481816597)
        ·
          refine ⟨8354877116114123085085153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178237378477101292481816597 8354877116114123085085153)
          ·
            refine ⟨6266157837085592313813865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8354877116114123085085153 6266157837085592313813865)
            ·
              refine ⟨4699618377814194235360399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6266157837085592313813865 4699618377814194235360399)
              ·
                refine ⟨7049427566721291353040599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699618377814194235360399 7049427566721291353040599)
                ·
                  refine ⟨10574141350081937029560899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049427566721291353040599 10574141350081937029560899)
                  ·
                    refine ⟨15861212025122905544341349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10574141350081937029560899 15861212025122905544341349)
                    ·
                      refine ⟨2973977254710544789564003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15861212025122905544341349 2973977254710544789564003)
                      ·
                        rfl

theorem cell23_5791800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_5791800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791800 prefixEnd_5791800 := by exact prefixLift 5791800
  have htrace : WordTrace (prefixWord ++ tailWord_5791800) baseStart_5791800 baseEnd_5791800 := by
    simpa [prefixWord, tailWord_5791800, baseEnd_5791800] using wordTrace_append hprefix tailTrace_5791800
  have hstable : (prefixWord ++ tailWord_5791800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791800).length < 2 ^ (prefixWord ++ tailWord_5791800).sum := by decide
  have hdescent : baseEnd_5791800 < baseStart_5791800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791806 : List Nat := [4, 2, 1, 3, 2, 1, 10]
def baseStart_5791806 : Nat := 118140960795 + 5791806 * 2 ^ 59
def prefixEnd_5791806 : Nat := 4983230072969 + 3 ^ 40 * 5791806 * 2
def baseEnd_5791806 : Nat := 36715806612277429210975

theorem tailTrace_5791806 : CollatzResearch.WordTrace tailWord_5791806 prefixEnd_5791806 36715806612277429210975 := by
  unfold tailWord_5791806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26405564906910437319840409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140829679503522332372482181 26405564906910437319840409)
  ·
    refine ⟨19804173680182827989880307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26405564906910437319840409 19804173680182827989880307)
    ·
      refine ⟨29706260520274241984820461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19804173680182827989880307 29706260520274241984820461)
      ·
        refine ⟨11139847695102840744307673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29706260520274241984820461 11139847695102840744307673)
        ·
          refine ⟨8354885771327130558230755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11139847695102840744307673 8354885771327130558230755)
          ·
            refine ⟨12532328656990695837346133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8354885771327130558230755 12532328656990695837346133)
            ·
              refine ⟨36715806612277429210975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12532328656990695837346133 36715806612277429210975)
              ·
                rfl

theorem cell23_5791806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 10].length) (baseStart_5791806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791806 prefixEnd_5791806 := by exact prefixLift 5791806
  have htrace : WordTrace (prefixWord ++ tailWord_5791806) baseStart_5791806 baseEnd_5791806 := by
    simpa [prefixWord, tailWord_5791806, baseEnd_5791806] using wordTrace_append hprefix tailTrace_5791806
  have hstable : (prefixWord ++ tailWord_5791806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791806).length < 2 ^ (prefixWord ++ tailWord_5791806).sum := by decide
  have hdescent : baseEnd_5791806 < baseStart_5791806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791830 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5791830 : Nat := 118140960795 + 5791830 * 2 ^ 59
def prefixEnd_5791830 : Nat := 4983230072969 + 3 ^ 40 * 5791830 * 2
def baseEnd_5791830 : Nat := 2973992659130179672188865

theorem tailTrace_5791830 : CollatzResearch.WordTrace tailWord_5791830 prefixEnd_5791830 2973992659130179672188865 := by
  unfold tailWord_5791830
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202837162949784416099809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140830263071464367105064629 13202837162949784416099809)
  ·
    refine ⟨9902127872212338312074857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13202837162949784416099809 9902127872212338312074857)
    ·
      refine ⟨7426595904159253734056143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9902127872212338312074857 7426595904159253734056143)
      ·
        refine ⟨11139893856238880601084215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7426595904159253734056143 11139893856238880601084215)
        ·
          refine ⟨16709840784358320901626323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11139893856238880601084215 16709840784358320901626323)
          ·
            refine ⟨25064761176537481352439485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16709840784358320901626323 25064761176537481352439485)
            ·
              refine ⟨9399285441201555507164807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25064761176537481352439485 9399285441201555507164807)
              ·
                refine ⟨14098928161802333260747211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399285441201555507164807 14098928161802333260747211)
                ·
                  refine ⟨21148392242703499891120817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14098928161802333260747211 21148392242703499891120817)
                  ·
                    refine ⟨15861294182027624918340613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21148392242703499891120817 15861294182027624918340613)
                    ·
                      refine ⟨2973992659130179672188865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15861294182027624918340613 2973992659130179672188865)
                      ·
                        rfl

theorem cell23_5791830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5791830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791830 prefixEnd_5791830 := by exact prefixLift 5791830
  have htrace : WordTrace (prefixWord ++ tailWord_5791830) baseStart_5791830 baseEnd_5791830 := by
    simpa [prefixWord, tailWord_5791830, baseEnd_5791830] using wordTrace_append hprefix tailTrace_5791830
  have hstable : (prefixWord ++ tailWord_5791830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791830).length < 2 ^ (prefixWord ++ tailWord_5791830).sum := by decide
  have hdescent : baseEnd_5791830 < baseStart_5791830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791843 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5791843 : Nat := 118140960795 + 5791843 * 2 ^ 59
def prefixEnd_5791843 : Nat := 4983230072969 + 3 ^ 40 * 5791843 * 2
def baseEnd_5791843 : Nat := 2973999334378688121326305

theorem tailTrace_5791843 : CollatzResearch.WordTrace tailWord_5791843 prefixEnd_5791843 2973999334378688121326305 := by
  unfold tailWord_5791843
  simp only [CollatzResearch.WordTrace]
  refine ⟨211245868756149453877820183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140830579170766302585213455 211245868756149453877820183)
  ·
    refine ⟨316868803134224180816730275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211245868756149453877820183 316868803134224180816730275)
    ·
      refine ⟨475303204701336271225095413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316868803134224180816730275 475303204701336271225095413)
      ·
        refine ⟨44559675440750275427352695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 475303204701336271225095413 44559675440750275427352695)
        ·
          refine ⟨66839513161125413141029043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44559675440750275427352695 66839513161125413141029043)
          ·
            refine ⟨100259269741688119711543565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66839513161125413141029043 100259269741688119711543565)
            ·
              refine ⟨37597226153133044891828837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100259269741688119711543565 37597226153133044891828837)
              ·
                refine ⟨7049479903712445917217907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37597226153133044891828837 7049479903712445917217907)
                ·
                  refine ⟨10574219855568668875826861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049479903712445917217907 10574219855568668875826861)
                  ·
                    refine ⟨3965332445838250828435073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10574219855568668875826861 3965332445838250828435073)
                    ·
                      refine ⟨2973999334378688121326305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965332445838250828435073 2973999334378688121326305)
                      ·
                        rfl

theorem cell23_5791843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5791843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791843 prefixEnd_5791843 := by exact prefixLift 5791843
  have htrace : WordTrace (prefixWord ++ tailWord_5791843) baseStart_5791843 baseEnd_5791843 := by
    simpa [prefixWord, tailWord_5791843, baseEnd_5791843] using wordTrace_append hprefix tailTrace_5791843
  have hstable : (prefixWord ++ tailWord_5791843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791843).length < 2 ^ (prefixWord ++ tailWord_5791843).sum := by decide
  have hdescent : baseEnd_5791843 < baseStart_5791843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791876 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5791876 : Nat := 118140960795 + 5791876 * 2 ^ 59
def prefixEnd_5791876 : Nat := 4983230072969 + 3 ^ 40 * 5791876 * 2
def baseEnd_5791876 : Nat := 2974016279240286492213653

theorem tailTrace_5791876 : CollatzResearch.WordTrace tailWord_5791876 prefixEnd_5791876 2974016279240286492213653 := by
  unfold tailWord_5791876
  simp only [CollatzResearch.WordTrace]
  refine ⟨105623536182514950256885741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140831381576686600342514321 105623536182514950256885741)
  ·
    refine ⟨39608826068443106346332153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105623536182514950256885741 39608826068443106346332153)
    ·
      refine ⟨29706619551332329759749115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39608826068443106346332153 29706619551332329759749115)
      ·
        refine ⟨44559929326998494639623673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29706619551332329759749115 44559929326998494639623673)
        ·
          refine ⟨33419946995248870979717755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44559929326998494639623673 33419946995248870979717755)
          ·
            refine ⟨50129920492873306469576633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33419946995248870979717755 50129920492873306469576633)
            ·
              refine ⟨37597440369654979852182475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50129920492873306469576633 37597440369654979852182475)
              ·
                refine ⟨56396160554482469778273713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37597440369654979852182475 56396160554482469778273713)
                ·
                  refine ⟨42297120415861852333705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56396160554482469778273713 42297120415861852333705285)
                  ·
                    refine ⟨7930710077974097312569741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42297120415861852333705285 7930710077974097312569741)
                    ·
                      refine ⟨2974016279240286492213653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7930710077974097312569741 2974016279240286492213653)
                      ·
                        rfl

theorem cell23_5791876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5791876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791876 prefixEnd_5791876 := by exact prefixLift 5791876
  have htrace : WordTrace (prefixWord ++ tailWord_5791876) baseStart_5791876 baseEnd_5791876 := by
    simpa [prefixWord, tailWord_5791876, baseEnd_5791876] using wordTrace_append hprefix tailTrace_5791876
  have hstable : (prefixWord ++ tailWord_5791876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791876).length < 2 ^ (prefixWord ++ tailWord_5791876).sum := by decide
  have hdescent : baseEnd_5791876 < baseStart_5791876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791936 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_5791936 : Nat := 118140960795 + 5791936 * 2 ^ 59
def prefixEnd_5791936 : Nat := 4983230072969 + 3 ^ 40 * 5791936 * 2
def baseEnd_5791936 : Nat := 2974047088079556257463377

theorem tailTrace_5791936 : CollatzResearch.WordTrace tailWord_5791936 prefixEnd_5791936 2974047088079556257463377 := by
  unfold tailWord_5791936
  simp only [CollatzResearch.WordTrace]
  refine ⟨105624630372406265380477831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140832840496541687173970441 105624630372406265380477831)
  ·
    refine ⟨158436945558609398070716747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105624630372406265380477831 158436945558609398070716747)
    ·
      refine ⟨237655418337914097106075121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158436945558609398070716747 237655418337914097106075121)
      ·
        refine ⟨178241563753435572829556341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237655418337914097106075121 178241563753435572829556341)
        ·
          refine ⟨16710146601884584952770907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178241563753435572829556341 16710146601884584952770907)
          ·
            refine ⟨25065219902826877429156361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16710146601884584952770907 25065219902826877429156361)
            ·
              refine ⟨18798914927120158071867271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25065219902826877429156361 18798914927120158071867271)
              ·
                refine ⟨28198372390680237107800907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18798914927120158071867271 28198372390680237107800907)
                ·
                  refine ⟨42297558586020355661701361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28198372390680237107800907 42297558586020355661701361)
                  ·
                    refine ⟨31723168939515266746276021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42297558586020355661701361 31723168939515266746276021)
                    ·
                      refine ⟨2974047088079556257463377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31723168939515266746276021 2974047088079556257463377)
                      ·
                        rfl

theorem cell23_5791936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_5791936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791936 prefixEnd_5791936 := by exact prefixLift 5791936
  have htrace : WordTrace (prefixWord ++ tailWord_5791936) baseStart_5791936 baseEnd_5791936 := by
    simpa [prefixWord, tailWord_5791936, baseEnd_5791936] using wordTrace_append hprefix tailTrace_5791936
  have hstable : (prefixWord ++ tailWord_5791936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791936).length < 2 ^ (prefixWord ++ tailWord_5791936).sum := by decide
  have hdescent : baseEnd_5791936 < baseStart_5791936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791946 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_5791946 : Nat := 118140960795 + 5791946 * 2 ^ 59
def prefixEnd_5791946 : Nat := 4983230072969 + 3 ^ 40 * 5791946 * 2
def baseEnd_5791946 : Nat := 2974052222886101218338331

theorem tailTrace_5791946 : CollatzResearch.WordTrace tailWord_5791946 prefixEnd_5791946 2974052222886101218338331 := by
  unfold tailWord_5791946
  simp only [CollatzResearch.WordTrace]
  refine ⟨52812406368694075617204923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140833083649850868312546461 52812406368694075617204923)
  ·
    refine ⟨79218609553041113425807385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52812406368694075617204923 79218609553041113425807385)
    ·
      refine ⟨59413957164780835069355539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79218609553041113425807385 59413957164780835069355539)
      ·
        refine ⟨89120935747171252604033309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59413957164780835069355539 89120935747171252604033309)
        ·
          refine ⟨33420350905189219726512491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89120935747171252604033309 33420350905189219726512491)
          ·
            refine ⟨50130526357783829589768737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33420350905189219726512491 50130526357783829589768737)
            ·
              refine ⟨37597894768337872192326553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50130526357783829589768737 37597894768337872192326553)
              ·
                refine ⟨28198421076253404144244915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37597894768337872192326553 28198421076253404144244915)
                ·
                  refine ⟨42297631614380106216367373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28198421076253404144244915 42297631614380106216367373)
                  ·
                    refine ⟨15861611855392539831137765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42297631614380106216367373 15861611855392539831137765)
                    ·
                      refine ⟨2974052222886101218338331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15861611855392539831137765 2974052222886101218338331)
                      ·
                        rfl

theorem cell23_5791946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_5791946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791946 prefixEnd_5791946 := by exact prefixLift 5791946
  have htrace : WordTrace (prefixWord ++ tailWord_5791946) baseStart_5791946 baseEnd_5791946 := by
    simpa [prefixWord, tailWord_5791946, baseEnd_5791946] using wordTrace_append hprefix tailTrace_5791946
  have hstable : (prefixWord ++ tailWord_5791946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791946).length < 2 ^ (prefixWord ++ tailWord_5791946).sum := by decide
  have hdescent : baseEnd_5791946 < baseStart_5791946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5791976 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5791976 : Nat := 118140960795 + 5791976 * 2 ^ 59
def prefixEnd_5791976 : Nat := 4983230072969 + 3 ^ 40 * 5791976 * 2
def baseEnd_5791976 : Nat := 2974067627305736100963193

theorem tailTrace_5791976 : CollatzResearch.WordTrace tailWord_5791976 prefixEnd_5791976 2974067627305736100963193 := by
  unfold tailWord_5791976
  simp only [CollatzResearch.WordTrace]
  refine ⟨105625359832333808796205891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140833813109778411728274521 105625359832333808796205891)
  ·
    refine ⟨158438039748500713194308837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105625359832333808796205891 158438039748500713194308837)
    ·
      refine ⟨29707132452843883723932907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158438039748500713194308837 29707132452843883723932907)
      ·
        refine ⟨44560698679265825585899361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29707132452843883723932907 44560698679265825585899361)
        ·
          refine ⟨33420524009449369189424521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44560698679265825585899361 33420524009449369189424521)
          ·
            refine ⟨25065393007087026892068391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33420524009449369189424521 25065393007087026892068391)
            ·
              refine ⟨37598089510630540338102587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25065393007087026892068391 37598089510630540338102587)
              ·
                refine ⟨56397134265945810507153881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37598089510630540338102587 56397134265945810507153881)
                ·
                  refine ⟨42297850699459357880365411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56397134265945810507153881 42297850699459357880365411)
                  ·
                    refine ⟨63446776049189036820548117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42297850699459357880365411 63446776049189036820548117)
                    ·
                      refine ⟨2974067627305736100963193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63446776049189036820548117 2974067627305736100963193)
                      ·
                        rfl

theorem cell23_5791976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5791976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5791976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5791976 prefixEnd_5791976 := by exact prefixLift 5791976
  have htrace : WordTrace (prefixWord ++ tailWord_5791976) baseStart_5791976 baseEnd_5791976 := by
    simpa [prefixWord, tailWord_5791976, baseEnd_5791976] using wordTrace_append hprefix tailTrace_5791976
  have hstable : (prefixWord ++ tailWord_5791976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5791976).length < 2 ^ (prefixWord ++ tailWord_5791976).sum := by decide
  have hdescent : baseEnd_5791976 < baseStart_5791976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5791976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792003 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 6]
def baseStart_5792003 : Nat := 118140960795 + 5792003 * 2 ^ 59
def prefixEnd_5792003 : Nat := 4983230072969 + 3 ^ 40 * 5792003 * 2
def baseEnd_5792003 : Nat := 330453499031489721702841

theorem tailTrace_5792003 : CollatzResearch.WordTrace tailWord_5792003 prefixEnd_5792003 330453499031489721702841 := by
  unfold tailWord_5792003
  simp only [CollatzResearch.WordTrace]
  refine ⟨211251704435569801203644663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140834469623713200802429775 211251704435569801203644663)
  ·
    refine ⟨316877556653354701805466995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211251704435569801203644663 316877556653354701805466995)
    ·
      refine ⟨475316334980032052708200493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316877556653354701805466995 475316334980032052708200493)
      ·
        refine ⟨178243625617512019765575185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475316334980032052708200493 178243625617512019765575185)
        ·
          refine ⟨133682719213134014824181389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178243625617512019765575185 133682719213134014824181389)
          ·
            refine ⟨50131019704925255559068021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133682719213134014824181389 50131019704925255559068021)
            ·
              refine ⟨4699783097336742708662627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50131019704925255559068021 4699783097336742708662627)
              ·
                refine ⟨7049674646005114062993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699783097336742708662627 7049674646005114062993941)
                ·
                  refine ⟨330453499031489721702841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7049674646005114062993941 330453499031489721702841)
                  ·
                    rfl

theorem cell23_5792003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 6].length) (baseStart_5792003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792003 prefixEnd_5792003 := by exact prefixLift 5792003
  have htrace : WordTrace (prefixWord ++ tailWord_5792003) baseStart_5792003 baseEnd_5792003 := by
    simpa [prefixWord, tailWord_5792003, baseEnd_5792003] using wordTrace_append hprefix tailTrace_5792003
  have hstable : (prefixWord ++ tailWord_5792003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792003).length < 2 ^ (prefixWord ++ tailWord_5792003).sum := by decide
  have hdescent : baseEnd_5792003 < baseStart_5792003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792033 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_5792033 : Nat := 118140960795 + 5792033 * 2 ^ 59
def prefixEnd_5792033 : Nat := 4983230072969 + 3 ^ 40 * 5792033 * 2
def baseEnd_5792033 : Nat := 991365631901014125983477

theorem tailTrace_5792033 : CollatzResearch.WordTrace tailWord_5792033 prefixEnd_5792033 991365631901014125983477 := by
  unfold tailWord_5792033
  simp only [CollatzResearch.WordTrace]
  refine ⟨211252798625461116327236753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140835199083640744218157835 211252798625461116327236753)
  ·
    refine ⟨158439598969095837245427565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211252798625461116327236753 158439598969095837245427565)
    ·
      refine ⟨59414849613410938967035337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158439598969095837245427565 59414849613410938967035337)
      ·
        refine ⟨44561137210058204225276503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59414849613410938967035337 44561137210058204225276503)
        ·
          refine ⟨66841705815087306337914755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44561137210058204225276503 66841705815087306337914755)
          ·
            refine ⟨100262558722630959506872133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66841705815087306337914755 100262558722630959506872133)
            ·
              refine ⟨18799229760493304907538525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100262558722630959506872133 18799229760493304907538525)
              ·
                refine ⟨7049711160184989340326947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18799229760493304907538525 7049711160184989340326947)
                ·
                  refine ⟨10574566740277484010490421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049711160184989340326947 10574566740277484010490421)
                  ·
                    refine ⟨991365631901014125983477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10574566740277484010490421 991365631901014125983477)
                    ·
                      rfl

theorem cell23_5792033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_5792033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792033 prefixEnd_5792033 := by exact prefixLift 5792033
  have htrace : WordTrace (prefixWord ++ tailWord_5792033) baseStart_5792033 baseEnd_5792033 := by
    simpa [prefixWord, tailWord_5792033, baseEnd_5792033] using wordTrace_append hprefix tailTrace_5792033
  have hstable : (prefixWord ++ tailWord_5792033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792033).length < 2 ^ (prefixWord ++ tailWord_5792033).sum := by decide
  have hdescent : baseEnd_5792033 < baseStart_5792033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792053 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_5792053 : Nat := 118140960795 + 5792053 * 2 ^ 59
def prefixEnd_5792053 : Nat := 4983230072969 + 3 ^ 40 * 5792053 * 2
def baseEnd_5792053 : Nat := 2974107165316132299700339

theorem tailTrace_5792053 : CollatzResearch.WordTrace tailWord_5792053 prefixEnd_5792053 2974107165316132299700339 := by
  unfold tailWord_5792053
  simp only [CollatzResearch.WordTrace]
  refine ⟨211253528085388659742964813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140835685390259106495309875 211253528085388659742964813)
  ·
    refine ⟨79220073032020747403611805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211253528085388659742964813 79220073032020747403611805)
    ·
      refine ⟨29707527387007780276354427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79220073032020747403611805 29707527387007780276354427)
      ·
        refine ⟨44561291080511670414531641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29707527387007780276354427 44561291080511670414531641)
        ·
          refine ⟨33420968310383752810898731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44561291080511670414531641 33420968310383752810898731)
          ·
            refine ⟨50131452465575629216348097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33420968310383752810898731 50131452465575629216348097)
            ·
              refine ⟨37598589349181721912261073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50131452465575629216348097 37598589349181721912261073)
              ·
                refine ⟨28198942011886291434195805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37598589349181721912261073 28198942011886291434195805)
                ·
                  refine ⟨10574603254457359287823427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28198942011886291434195805 10574603254457359287823427)
                  ·
                    refine ⟨15861904881686038931735141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10574603254457359287823427 15861904881686038931735141)
                    ·
                      refine ⟨2974107165316132299700339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15861904881686038931735141 2974107165316132299700339)
                      ·
                        rfl

theorem cell23_5792053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_5792053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792053 prefixEnd_5792053 := by exact prefixLift 5792053
  have htrace : WordTrace (prefixWord ++ tailWord_5792053) baseStart_5792053 baseEnd_5792053 := by
    simpa [prefixWord, tailWord_5792053, baseEnd_5792053] using wordTrace_append hprefix tailTrace_5792053
  have hstable : (prefixWord ++ tailWord_5792053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792053).length < 2 ^ (prefixWord ++ tailWord_5792053).sum := by decide
  have hdescent : baseEnd_5792053 < baseStart_5792053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792076 : List Nat := [2, 2, 1, 3, 2, 1, 1, 11]
def baseStart_5792076 : Nat := 118140960795 + 5792076 * 2 ^ 59
def prefixEnd_5792076 : Nat := 4983230072969 + 3 ^ 40 * 5792076 * 2
def baseEnd_5792076 : Nat := 110152554643377248507879

theorem tailTrace_5792076 : CollatzResearch.WordTrace tailWord_5792076 prefixEnd_5792076 110152554643377248507879 := by
  unfold tailWord_5792076
  simp only [CollatzResearch.WordTrace]
  refine ⟨105627183482152667335526041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140836244642870223114034721 105627183482152667335526041)
  ·
    refine ⟨79220387611614500501644531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105627183482152667335526041 79220387611614500501644531)
    ·
      refine ⟨118830581417421750752466797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79220387611614500501644531 118830581417421750752466797)
      ·
        refine ⟨44561468031533156532175049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118830581417421750752466797 44561468031533156532175049)
        ·
          refine ⟨33421101023649867399131287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44561468031533156532175049 33421101023649867399131287)
          ·
            refine ⟨50131651535474801098696931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33421101023649867399131287 50131651535474801098696931)
            ·
              refine ⟨75197477303212201648045397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50131651535474801098696931 75197477303212201648045397)
              ·
                refine ⟨110152554643377248507879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75197477303212201648045397 110152554643377248507879)
                ·
                  rfl

theorem cell23_5792076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 11].length) (baseStart_5792076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792076 prefixEnd_5792076 := by exact prefixLift 5792076
  have htrace : WordTrace (prefixWord ++ tailWord_5792076) baseStart_5792076 baseEnd_5792076 := by
    simpa [prefixWord, tailWord_5792076, baseEnd_5792076] using wordTrace_append hprefix tailTrace_5792076
  have hstable : (prefixWord ++ tailWord_5792076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792076).length < 2 ^ (prefixWord ++ tailWord_5792076).sum := by decide
  have hdescent : baseEnd_5792076 < baseStart_5792076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792093 : List Nat := [1, 4, 5, 13]
def baseStart_5792093 : Nat := 118140960795 + 5792093 * 2 ^ 59
def prefixEnd_5792093 : Nat := 4983230072969 + 3 ^ 40 * 5792093 * 2
def baseEnd_5792093 : Nat := 1359912073407550134065

theorem tailTrace_5792093 : CollatzResearch.WordTrace tailWord_5792093 prefixEnd_5792093 1359912073407550134065 := by
  unfold tailWord_5792093
  simp only [CollatzResearch.WordTrace]
  refine ⟨211254987005243746574420933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140836658003495831049613955 211254987005243746574420933)
  ·
    refine ⟨39610310063483202482703925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211254987005243746574420933 39610310063483202482703925)
    ·
      refine ⟨3713466568451550232753493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39610310063483202482703925 3713466568451550232753493)
      ·
        refine ⟨1359912073407550134065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3713466568451550232753493 1359912073407550134065)
        ·
          rfl

theorem cell23_5792093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 13].length) (baseStart_5792093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792093 prefixEnd_5792093 := by exact prefixLift 5792093
  have htrace : WordTrace (prefixWord ++ tailWord_5792093) baseStart_5792093 baseEnd_5792093 := by
    simpa [prefixWord, tailWord_5792093, baseEnd_5792093] using wordTrace_append hprefix tailTrace_5792093
  have hstable : (prefixWord ++ tailWord_5792093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792093).length < 2 ^ (prefixWord ++ tailWord_5792093).sum := by decide
  have hdescent : baseEnd_5792093 < baseStart_5792093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792138 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5792138 : Nat := 118140960795 + 5792138 * 2 ^ 59
def prefixEnd_5792138 : Nat := 4983230072969 + 3 ^ 40 * 5792138 * 2
def baseEnd_5792138 : Nat := 2974150811171764467137449

theorem tailTrace_5792138 : CollatzResearch.WordTrace tailWord_5792138 prefixEnd_5792138 2974150811171764467137449 := by
  unfold tailWord_5792138
  simp only [CollatzResearch.WordTrace]
  refine ⟨52814157072520179814952267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140837752193387146173206045 52814157072520179814952267)
  ·
    refine ⟨79221235608780269722428401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52814157072520179814952267 79221235608780269722428401)
    ·
      refine ⟨59415926706585202291821301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79221235608780269722428401 59415926706585202291821301)
      ·
        refine ⟨5570243128742362714858247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59415926706585202291821301 5570243128742362714858247)
        ·
          refine ⟨8355364693113544072287371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570243128742362714858247 8355364693113544072287371)
          ·
            refine ⟨12533047039670316108431057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355364693113544072287371 12533047039670316108431057)
            ·
              refine ⟨9399785279752737081323293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12533047039670316108431057 9399785279752737081323293)
              ·
                refine ⟨3524919479907276405496235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9399785279752737081323293 3524919479907276405496235)
                ·
                  refine ⟨5287379219860914608244353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524919479907276405496235 5287379219860914608244353)
                  ·
                    refine ⟨3965534414895685956183265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5287379219860914608244353 3965534414895685956183265)
                    ·
                      refine ⟨2974150811171764467137449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965534414895685956183265 2974150811171764467137449)
                      ·
                        rfl

theorem cell23_5792138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5792138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792138 prefixEnd_5792138 := by exact prefixLift 5792138
  have htrace : WordTrace (prefixWord ++ tailWord_5792138) baseStart_5792138 baseEnd_5792138 := by
    simpa [prefixWord, tailWord_5792138, baseEnd_5792138] using wordTrace_append hprefix tailTrace_5792138
  have hstable : (prefixWord ++ tailWord_5792138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792138).length < 2 ^ (prefixWord ++ tailWord_5792138).sum := by decide
  have hdescent : baseEnd_5792138 < baseStart_5792138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792154 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5792154 : Nat := 118140960795 + 5792154 * 2 ^ 59
def prefixEnd_5792154 : Nat := 4983230072969 + 3 ^ 40 * 5792154 * 2
def baseEnd_5792154 : Nat := 2974159026862236404537375

theorem tailTrace_5792154 : CollatzResearch.WordTrace tailWord_5792154 prefixEnd_5792154 2974159026862236404537375 := by
  unfold tailWord_5792154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52814302964505688498097879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140838141238681835994927677 52814302964505688498097879)
  ·
    refine ⟨79221454446758532747146819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52814302964505688498097879 79221454446758532747146819)
    ·
      refine ⟨118832181670137799120720229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79221454446758532747146819 118832181670137799120720229)
      ·
        refine ⟨22281034063150837335135043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118832181670137799120720229 22281034063150837335135043)
        ·
          refine ⟨33421551094726256002702565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22281034063150837335135043 33421551094726256002702565)
          ·
            refine ⟨6266540830261173000506731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33421551094726256002702565 6266540830261173000506731)
            ·
              refine ⟨9399811245391759500760097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266540830261173000506731 9399811245391759500760097)
              ·
                refine ⟨7049858434043819625570073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9399811245391759500760097 7049858434043819625570073)
                ·
                  refine ⟨5287393825532864719177555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7049858434043819625570073 5287393825532864719177555)
                  ·
                    refine ⟨7931090738299297078766333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287393825532864719177555 7931090738299297078766333)
                    ·
                      refine ⟨2974159026862236404537375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931090738299297078766333 2974159026862236404537375)
                      ·
                        rfl

theorem cell23_5792154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5792154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792154 prefixEnd_5792154 := by exact prefixLift 5792154
  have htrace : WordTrace (prefixWord ++ tailWord_5792154) baseStart_5792154 baseEnd_5792154 := by
    simpa [prefixWord, tailWord_5792154, baseEnd_5792154] using wordTrace_append hprefix tailTrace_5792154
  have hstable : (prefixWord ++ tailWord_5792154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792154).length < 2 ^ (prefixWord ++ tailWord_5792154).sum := by decide
  have hdescent : baseEnd_5792154 < baseStart_5792154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792177 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_5792177 : Nat := 118140960795 + 5792177 * 2 ^ 59
def prefixEnd_5792177 : Nat := 4983230072969 + 3 ^ 40 * 5792177 * 2
def baseEnd_5792177 : Nat := 2974170836917289814549769

theorem tailTrace_5792177 : CollatzResearch.WordTrace tailWord_5792177 prefixEnd_5792177 2974170836917289814549769 := by
  unfold tailWord_5792177
  simp only [CollatzResearch.WordTrace]
  refine ⟨211258050736939428920478785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140838700491292952613652523 211258050736939428920478785)
  ·
    refine ⟨158443538052704571690359089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211258050736939428920478785 158443538052704571690359089)
    ·
      refine ⟨118832653539528428767769317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158443538052704571690359089 118832653539528428767769317)
      ·
        refine ⟨22281122538661580393956747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118832653539528428767769317 22281122538661580393956747)
        ·
          refine ⟨33421683807992370590935121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22281122538661580393956747 33421683807992370590935121)
          ·
            refine ⟨25066262855994277943201341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33421683807992370590935121 25066262855994277943201341)
            ·
              refine ⟨9399848570997854228700503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25066262855994277943201341 9399848570997854228700503)
              ·
                refine ⟨14099772856496781343050755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399848570997854228700503 14099772856496781343050755)
                ·
                  refine ⟨21149659284745172014576133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14099772856496781343050755 21149659284745172014576133)
                  ·
                    refine ⟨3965561115889719752733025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21149659284745172014576133 3965561115889719752733025)
                    ·
                      refine ⟨2974170836917289814549769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965561115889719752733025 2974170836917289814549769)
                      ·
                        rfl

theorem cell23_5792177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_5792177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792177 prefixEnd_5792177 := by exact prefixLift 5792177
  have htrace : WordTrace (prefixWord ++ tailWord_5792177) baseStart_5792177 baseEnd_5792177 := by
    simpa [prefixWord, tailWord_5792177, baseEnd_5792177] using wordTrace_append hprefix tailTrace_5792177
  have hstable : (prefixWord ++ tailWord_5792177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792177).length < 2 ^ (prefixWord ++ tailWord_5792177).sum := by decide
  have hdescent : baseEnd_5792177 < baseStart_5792177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792183 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 7]
def baseStart_5792183 : Nat := 118140960795 + 5792183 * 2 ^ 59
def prefixEnd_5792183 : Nat := 4983230072969 + 3 ^ 40 * 5792183 * 2
def baseEnd_5792183 : Nat := 330463768644579643452749

theorem tailTrace_5792183 : CollatzResearch.WordTrace tailWord_5792183 prefixEnd_5792183 330463768644579643452749 := by
  unfold tailWord_5792183
  simp only [CollatzResearch.WordTrace]
  refine ⟨211258269574917691945197203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140838846383278461296798135 211258269574917691945197203)
  ·
    refine ⟨316887404362376537917795805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211258269574917691945197203 316887404362376537917795805)
    ·
      refine ⟨118832776635891201719173427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316887404362376537917795805 118832776635891201719173427)
      ·
        refine ⟨178249164953836802578760141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118832776635891201719173427 178249164953836802578760141)
        ·
          refine ⟨66843436857688800967035053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178249164953836802578760141 66843436857688800967035053)
          ·
            refine ⟨25066288821633300362638145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66843436857688800967035053 25066288821633300362638145)
            ·
              refine ⟨18799716616224975271978609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25066288821633300362638145 18799716616224975271978609)
              ·
                refine ⟨14099787462168731453983957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18799716616224975271978609 14099787462168731453983957)
                ·
                  refine ⟨330463768644579643452749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14099787462168731453983957 330463768644579643452749)
                  ·
                    rfl

theorem cell23_5792183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 7].length) (baseStart_5792183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792183 prefixEnd_5792183 := by exact prefixLift 5792183
  have htrace : WordTrace (prefixWord ++ tailWord_5792183) baseStart_5792183 baseEnd_5792183 := by
    simpa [prefixWord, tailWord_5792183, baseEnd_5792183] using wordTrace_append hprefix tailTrace_5792183
  have hstable : (prefixWord ++ tailWord_5792183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792183).length < 2 ^ (prefixWord ++ tailWord_5792183).sum := by decide
  have hdescent : baseEnd_5792183 < baseStart_5792183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792217 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 5]
def baseStart_5792217 : Nat := 118140960795 + 5792217 * 2 ^ 59
def prefixEnd_5792217 : Nat := 4983230072969 + 3 ^ 40 * 5792217 * 2
def baseEnd_5792217 : Nat := 330465708460385517561065

theorem tailTrace_5792217 : CollatzResearch.WordTrace tailWord_5792217 prefixEnd_5792217 330465708460385517561065 := by
  unfold tailWord_5792217
  simp only [CollatzResearch.WordTrace]
  refine ⟨211259509656794515751934905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140839673104529677167956603 211259509656794515751934905)
  ·
    refine ⟨158444632242595886813951179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211259509656794515751934905 158444632242595886813951179)
    ·
      refine ⟨237666948363893830220926769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158444632242595886813951179 237666948363893830220926769)
      ·
        refine ⟨178250211272920372665695077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237666948363893830220926769 178250211272920372665695077)
        ·
          refine ⟨33421914613672569874817827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178250211272920372665695077 33421914613672569874817827)
          ·
            refine ⟨50132871920508854812226741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33421914613672569874817827 50132871920508854812226741)
            ·
              refine ⟨4699956742547705138646257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50132871920508854812226741 4699956742547705138646257)
              ·
                refine ⟨3524967556910778853984693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699956742547705138646257 3524967556910778853984693)
                ·
                  refine ⟨330465708460385517561065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524967556910778853984693 330465708460385517561065)
                  ·
                    rfl

theorem cell23_5792217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 5].length) (baseStart_5792217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792217 prefixEnd_5792217 := by exact prefixLift 5792217
  have htrace : WordTrace (prefixWord ++ tailWord_5792217) baseStart_5792217 baseEnd_5792217 := by
    simpa [prefixWord, tailWord_5792217, baseEnd_5792217] using wordTrace_append hprefix tailTrace_5792217
  have hstable : (prefixWord ++ tailWord_5792217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792217).length < 2 ^ (prefixWord ++ tailWord_5792217).sum := by decide
  have hdescent : baseEnd_5792217 < baseStart_5792217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792223 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_5792223 : Nat := 118140960795 + 5792223 * 2 ^ 59
def prefixEnd_5792223 : Nat := 4983230072969 + 3 ^ 40 * 5792223 * 2
def baseEnd_5792223 : Nat := 2974194457027396634574557

theorem tailTrace_5792223 : CollatzResearch.WordTrace tailWord_5792223 prefixEnd_5792223 2974194457027396634574557 := by
  unfold tailWord_5792223
  simp only [CollatzResearch.WordTrace]
  refine ⟨211259728494772778776653323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140839818996515185851102215 211259728494772778776653323)
  ·
    refine ⟨316889592742159168164979985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211259728494772778776653323 316889592742159168164979985)
    ·
      refine ⟨237667194556619376123734989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316889592742159168164979985 237667194556619376123734989)
      ·
        refine ⟨89125197958732266046400621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237667194556619376123734989 89125197958732266046400621)
        ·
          refine ⟨33421949234524599767400233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89125197958732266046400621 33421949234524599767400233)
          ·
            refine ⟨25066461925893449825550175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33421949234524599767400233 25066461925893449825550175)
            ·
              refine ⟨37599692888840174738325263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25066461925893449825550175 37599692888840174738325263)
              ·
                refine ⟨56399539333260262107487895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37599692888840174738325263 56399539333260262107487895)
                ·
                  refine ⟨84599308999890393161231843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56399539333260262107487895 84599308999890393161231843)
                  ·
                    refine ⟨126898963499835589741847765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84599308999890393161231843 126898963499835589741847765)
                    ·
                      refine ⟨2974194457027396634574557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126898963499835589741847765 2974194457027396634574557)
                      ·
                        rfl

theorem cell23_5792223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_5792223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792223 prefixEnd_5792223 := by exact prefixLift 5792223
  have htrace : WordTrace (prefixWord ++ tailWord_5792223) baseStart_5792223 baseEnd_5792223 := by
    simpa [prefixWord, tailWord_5792223, baseEnd_5792223] using wordTrace_append hprefix tailTrace_5792223
  have hstable : (prefixWord ++ tailWord_5792223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792223).length < 2 ^ (prefixWord ++ tailWord_5792223).sum := by decide
  have hdescent : baseEnd_5792223 < baseStart_5792223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792233 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_5792233 : Nat := 118140960795 + 5792233 * 2 ^ 59
def prefixEnd_5792233 : Nat := 4983230072969 + 3 ^ 40 * 5792233 * 2
def baseEnd_5792233 : Nat := 2974199591833941595449511

theorem tailTrace_5792233 : CollatzResearch.WordTrace tailWord_5792233 prefixEnd_5792233 2974199591833941595449511 := by
  unfold tailWord_5792233
  simp only [CollatzResearch.WordTrace]
  refine ⟨211260093224736550484517353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140840062149824366989678235 211260093224736550484517353)
  ·
    refine ⟨158445069918552412863388015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211260093224736550484517353 158445069918552412863388015)
    ·
      refine ⟨237667604877828619295082023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158445069918552412863388015 237667604877828619295082023)
      ·
        refine ⟨356501407316742928942623035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237667604877828619295082023 356501407316742928942623035)
        ·
          refine ⟨534752110975114393413934553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356501407316742928942623035 534752110975114393413934553)
          ·
            refine ⟨401064083231335795060450915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534752110975114393413934553 401064083231335795060450915)
            ·
              refine ⟨601596124847003692590676373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401064083231335795060450915 601596124847003692590676373)
              ·
                refine ⟨28199818352203298090187955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 601596124847003692590676373 28199818352203298090187955)
                ·
                  refine ⟨42299727528304947135281933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28199818352203298090187955 42299727528304947135281933)
                  ·
                    refine ⟨15862397823114355175730725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42299727528304947135281933 15862397823114355175730725)
                    ·
                      refine ⟨2974199591833941595449511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15862397823114355175730725 2974199591833941595449511)
                      ·
                        rfl

theorem cell23_5792233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_5792233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792233 prefixEnd_5792233 := by exact prefixLift 5792233
  have htrace : WordTrace (prefixWord ++ tailWord_5792233) baseStart_5792233 baseEnd_5792233 := by
    simpa [prefixWord, tailWord_5792233, baseEnd_5792233] using wordTrace_append hprefix tailTrace_5792233
  have hstable : (prefixWord ++ tailWord_5792233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792233).length < 2 ^ (prefixWord ++ tailWord_5792233).sum := by decide
  have hdescent : baseEnd_5792233 < baseStart_5792233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792250 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_5792250 : Nat := 118140960795 + 5792250 * 2 ^ 59
def prefixEnd_5792250 : Nat := 4983230072969 + 3 ^ 40 * 5792250 * 2
def baseEnd_5792250 : Nat := 2974208321005068028936933

theorem tailTrace_5792250 : CollatzResearch.WordTrace tailWord_5792250 prefixEnd_5792250 2974208321005068028936933 := by
  unfold tailWord_5792250
  simp only [CollatzResearch.WordTrace]
  refine ⟨52815178316418740596971551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140840475510449974925257469 52815178316418740596971551)
  ·
    refine ⟨79222767474628110895457327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52815178316418740596971551 79222767474628110895457327)
    ·
      refine ⟨118834151211942166343185991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79222767474628110895457327 118834151211942166343185991)
      ·
        refine ⟨178251226817913249514778987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118834151211942166343185991 178251226817913249514778987)
        ·
          refine ⟨267376840226869874272168481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178251226817913249514778987 267376840226869874272168481)
          ·
            refine ⟨200532630170152405704126361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267376840226869874272168481 200532630170152405704126361)
            ·
              refine ⟨150399472627614304278094771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200532630170152405704126361 150399472627614304278094771)
              ·
                refine ⟨225599208941421456417142157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150399472627614304278094771 225599208941421456417142157)
                ·
                  refine ⟨84599703353033046156428309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225599208941421456417142157 84599703353033046156428309)
                  ·
                    refine ⟨3965611094673424038582577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84599703353033046156428309 3965611094673424038582577)
                    ·
                      refine ⟨2974208321005068028936933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965611094673424038582577 2974208321005068028936933)
                      ·
                        rfl

theorem cell23_5792250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_5792250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792250 prefixEnd_5792250 := by exact prefixLift 5792250
  have htrace : WordTrace (prefixWord ++ tailWord_5792250) baseStart_5792250 baseEnd_5792250 := by
    simpa [prefixWord, tailWord_5792250, baseEnd_5792250] using wordTrace_append hprefix tailTrace_5792250
  have hstable : (prefixWord ++ tailWord_5792250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792250).length < 2 ^ (prefixWord ++ tailWord_5792250).sum := by decide
  have hdescent : baseEnd_5792250 < baseStart_5792250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792301 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5792301 : Nat := 118140960795 + 5792301 * 2 ^ 59
def prefixEnd_5792301 : Nat := 4983230072969 + 3 ^ 40 * 5792301 * 2
def baseEnd_5792301 : Nat := 2974234508518447329399199

theorem tailTrace_5792301 : CollatzResearch.WordTrace tailWord_5792301 prefixEnd_5792301 2974234508518447329399199 := by
  unfold tailWord_5792301
  simp only [CollatzResearch.WordTrace]
  refine ⟨211262573388490198097992757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140841715592326798731995171 211262573388490198097992757)
  ·
    refine ⟨19805866255170956071686821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211262573388490198097992757 19805866255170956071686821)
    ·
      refine ⟨3713599922844554263441279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19805866255170956071686821 3713599922844554263441279)
      ·
        refine ⟨5570399884266831395161919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713599922844554263441279 5570399884266831395161919)
        ·
          refine ⟨8355599826400247092742879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570399884266831395161919 8355599826400247092742879)
          ·
            refine ⟨12533399739600370639114319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355599826400247092742879 12533399739600370639114319)
            ·
              refine ⟨18800099609400555958671479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12533399739600370639114319 18800099609400555958671479)
              ·
                refine ⟨28200149414100833938007219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18800099609400555958671479 28200149414100833938007219)
                ·
                  refine ⟨42300224121151250907010829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28200149414100833938007219 42300224121151250907010829)
                  ·
                    refine ⟨15862584045431719090129061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42300224121151250907010829 15862584045431719090129061)
                    ·
                      refine ⟨2974234508518447329399199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15862584045431719090129061 2974234508518447329399199)
                      ·
                        rfl

theorem cell23_5792301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5792301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792301 prefixEnd_5792301 := by exact prefixLift 5792301
  have htrace : WordTrace (prefixWord ++ tailWord_5792301) baseStart_5792301 baseEnd_5792301 := by
    simpa [prefixWord, tailWord_5792301, baseEnd_5792301] using wordTrace_append hprefix tailTrace_5792301
  have hstable : (prefixWord ++ tailWord_5792301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792301).length < 2 ^ (prefixWord ++ tailWord_5792301).sum := by decide
  have hdescent : baseEnd_5792301 < baseStart_5792301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792368 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 1, 1, 3]
def baseStart_5792368 : Nat := 118140960795 + 5792368 * 2 ^ 59
def prefixEnd_5792368 : Nat := 4983230072969 + 3 ^ 40 * 5792368 * 2
def baseEnd_5792368 : Nat := 2974268911722298567261391

theorem tailTrace_5792368 : CollatzResearch.WordTrace tailWord_5792368 prefixEnd_5792368 2974268911722298567261391 := by
  unfold tailWord_5792368
  simp only [CollatzResearch.WordTrace]
  refine ⟨105632508539623734270340879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140843344719498312360454505 105632508539623734270340879)
  ·
    refine ⟨158448762809435601405511319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105632508539623734270340879 158448762809435601405511319)
    ·
      refine ⟨237673144214153402108266979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158448762809435601405511319 237673144214153402108266979)
      ·
        refine ⟨356509716321230103162400469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237673144214153402108266979 356509716321230103162400469)
        ·
          refine ⟨8355696476278830542868761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 356509716321230103162400469 8355696476278830542868761)
          ·
            refine ⟨6266772357209122907151571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8355696476278830542868761 6266772357209122907151571)
            ·
              refine ⟨9400158535813684360727357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266772357209122907151571 9400158535813684360727357)
              ·
                refine ⟨3525059450930131635272759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9400158535813684360727357 3525059450930131635272759)
                ·
                  refine ⟨5287589176395197452909139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525059450930131635272759 5287589176395197452909139)
                  ·
                    refine ⟨7931383764592796179363709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287589176395197452909139 7931383764592796179363709)
                    ·
                      refine ⟨2974268911722298567261391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931383764592796179363709 2974268911722298567261391)
                      ·
                        rfl

theorem cell23_5792368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 1, 3].length) (baseStart_5792368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792368 prefixEnd_5792368 := by exact prefixLift 5792368
  have htrace : WordTrace (prefixWord ++ tailWord_5792368) baseStart_5792368 baseEnd_5792368 := by
    simpa [prefixWord, tailWord_5792368, baseEnd_5792368] using wordTrace_append hprefix tailTrace_5792368
  have hstable : (prefixWord ++ tailWord_5792368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792368).length < 2 ^ (prefixWord ++ tailWord_5792368).sum := by decide
  have hdescent : baseEnd_5792368 < baseStart_5792368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792377 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_5792377 : Nat := 118140960795 + 5792377 * 2 ^ 59
def prefixEnd_5792377 : Nat := 4983230072969 + 3 ^ 40 * 5792377 * 2
def baseEnd_5792377 : Nat := 2974273533048189032048849

theorem tailTrace_5792377 : CollatzResearch.WordTrace tailWord_5792377 prefixEnd_5792377 2974273533048189032048849 := by
  unfold tailWord_5792377
  simp only [CollatzResearch.WordTrace]
  refine ⟨211265345336214863077759385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140843563557476575385172923 211265345336214863077759385)
  ·
    refine ⟨158449009002161147308319539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211265345336214863077759385 158449009002161147308319539)
    ·
      refine ⟨237673513503241720962479309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158449009002161147308319539 237673513503241720962479309)
      ·
        refine ⟨89127567563715645360929741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237673513503241720962479309 89127567563715645360929741)
        ·
          refine ⟨33422837836393367010348653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89127567563715645360929741 33422837836393367010348653)
          ·
            refine ⟨12533564188647512628880745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33422837836393367010348653 12533564188647512628880745)
            ·
              refine ⟨9400173141485634471660559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12533564188647512628880745 9400173141485634471660559)
              ·
                refine ⟨14100259712228451707490839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9400173141485634471660559 14100259712228451707490839)
                ·
                  refine ⟨21150389568342677561236259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14100259712228451707490839 21150389568342677561236259)
                  ·
                    refine ⟨31725584352514016341854389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21150389568342677561236259 31725584352514016341854389)
                    ·
                      refine ⟨2974273533048189032048849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31725584352514016341854389 2974273533048189032048849)
                      ·
                        rfl

theorem cell23_5792377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_5792377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792377 prefixEnd_5792377 := by exact prefixLift 5792377
  have htrace : WordTrace (prefixWord ++ tailWord_5792377) baseStart_5792377 baseEnd_5792377 := by
    simpa [prefixWord, tailWord_5792377, baseEnd_5792377] using wordTrace_append hprefix tailTrace_5792377
  have hstable : (prefixWord ++ tailWord_5792377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792377).length < 2 ^ (prefixWord ++ tailWord_5792377).sum := by decide
  have hdescent : baseEnd_5792377 < baseStart_5792377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792407 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_5792407 : Nat := 118140960795 + 5792407 * 2 ^ 59
def prefixEnd_5792407 : Nat := 4983230072969 + 3 ^ 40 * 5792407 * 2
def baseEnd_5792407 : Nat := 2974288937467823914673711

theorem tailTrace_5792407 : CollatzResearch.WordTrace tailWord_5792407 prefixEnd_5792407 2974288937467823914673711 := by
  unfold tailWord_5792407
  simp only [CollatzResearch.WordTrace]
  refine ⟨211266439526106178201351475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140844293017404118800900983 211266439526106178201351475)
  ·
    refine ⟨316899659289159267302027213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211266439526106178201351475 316899659289159267302027213)
    ·
      refine ⟨118837372233434725238260205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316899659289159267302027213 118837372233434725238260205)
      ·
        refine ⟨44564014587538021964347577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118837372233434725238260205 44564014587538021964347577)
        ·
          refine ⟨33423010940653516473260683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44564014587538021964347577 33423010940653516473260683)
          ·
            refine ⟨50134516410980274709891025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33423010940653516473260683 50134516410980274709891025)
            ·
              refine ⟨37600887308235206032418269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50134516410980274709891025 37600887308235206032418269)
              ·
                refine ⟨14100332740588202262156851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37600887308235206032418269 14100332740588202262156851)
                ·
                  refine ⟨21150499110882303393235277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14100332740588202262156851 21150499110882303393235277)
                  ·
                    refine ⟨7931437166580863772463229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21150499110882303393235277 7931437166580863772463229)
                    ·
                      refine ⟨2974288937467823914673711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931437166580863772463229 2974288937467823914673711)
                      ·
                        rfl

theorem cell23_5792407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_5792407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792407 prefixEnd_5792407 := by exact prefixLift 5792407
  have htrace : WordTrace (prefixWord ++ tailWord_5792407) baseStart_5792407 baseEnd_5792407 := by
    simpa [prefixWord, tailWord_5792407, baseEnd_5792407] using wordTrace_append hprefix tailTrace_5792407
  have hstable : (prefixWord ++ tailWord_5792407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792407).length < 2 ^ (prefixWord ++ tailWord_5792407).sum := by decide
  have hdescent : baseEnd_5792407 < baseStart_5792407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792480 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_5792480 : Nat := 118140960795 + 5792480 * 2 ^ 59
def prefixEnd_5792480 : Nat := 4983230072969 + 3 ^ 40 * 5792480 * 2
def baseEnd_5792480 : Nat := 2974326421555602129060875

theorem tailTrace_5792480 : CollatzResearch.WordTrace tailWord_5792480 prefixEnd_5792480 2974326421555602129060875 := by
  unfold tailWord_5792480
  simp only [CollatzResearch.WordTrace]
  refine ⟨105634551027420855834379447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140846068036561141112505929 105634551027420855834379447)
  ·
    refine ⟨158451826541131283751569171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105634551027420855834379447 158451826541131283751569171)
    ·
      refine ⟨237677739811696925627353757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158451826541131283751569171 237677739811696925627353757)
      ·
        refine ⟨89129152429386347110257659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237677739811696925627353757 89129152429386347110257659)
        ·
          refine ⟨133693728644079520665386489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89129152429386347110257659 133693728644079520665386489)
          ·
            refine ⟨100270296483059640499039867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133693728644079520665386489 100270296483059640499039867)
            ·
              refine ⟨150405444724589460748559801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100270296483059640499039867 150405444724589460748559801)
              ·
                refine ⟨112804083543442095561419851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150405444724589460748559801 112804083543442095561419851)
                ·
                  refine ⟨169206125315163143342129777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112804083543442095561419851 169206125315163143342129777)
                  ·
                    refine ⟨126904593986372357506597333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169206125315163143342129777 126904593986372357506597333)
                    ·
                      refine ⟨2974326421555602129060875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126904593986372357506597333 2974326421555602129060875)
                      ·
                        rfl

theorem cell23_5792480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_5792480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792480 prefixEnd_5792480 := by exact prefixLift 5792480
  have htrace : WordTrace (prefixWord ++ tailWord_5792480) baseStart_5792480 baseEnd_5792480 := by
    simpa [prefixWord, tailWord_5792480, baseEnd_5792480] using wordTrace_append hprefix tailTrace_5792480
  have hstable : (prefixWord ++ tailWord_5792480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792480).length < 2 ^ (prefixWord ++ tailWord_5792480).sum := by decide
  have hdescent : baseEnd_5792480 < baseStart_5792480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792497 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_5792497 : Nat := 118140960795 + 5792497 * 2 ^ 59
def prefixEnd_5792497 : Nat := 4983230072969 + 3 ^ 40 * 5792497 * 2
def baseEnd_5792497 : Nat := 2974335150726728562548297

theorem tailTrace_5792497 : CollatzResearch.WordTrace tailWord_5792497 prefixEnd_5792497 2974335150726728562548297 := by
  unfold tailWord_5792497
  simp only [CollatzResearch.WordTrace]
  refine ⟨211269722095780123572127745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140846481397186749048085163 211269722095780123572127745)
  ·
    refine ⟨158452291571835092679095809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211269722095780123572127745 158452291571835092679095809)
    ·
      refine ⟨118839218678876319509321857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158452291571835092679095809 118839218678876319509321857)
      ·
        refine ⟨89129414009157239631991393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118839218678876319509321857 89129414009157239631991393)
        ·
          refine ⟨66847060506867929723993545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89129414009157239631991393 66847060506867929723993545)
          ·
            refine ⟨50135295380150947292995159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66847060506867929723993545 50135295380150947292995159)
            ·
              refine ⟨75202943070226420939492739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50135295380150947292995159 75202943070226420939492739)
              ·
                refine ⟨112804414605339631409239109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75202943070226420939492739 112804414605339631409239109)
                ·
                  refine ⟨21150827738501180889232333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112804414605339631409239109 21150827738501180889232333)
                  ·
                    refine ⟨7931560401937942833462125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21150827738501180889232333 7931560401937942833462125)
                    ·
                      refine ⟨2974335150726728562548297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931560401937942833462125 2974335150726728562548297)
                      ·
                        rfl

theorem cell23_5792497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_5792497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792497 prefixEnd_5792497 := by exact prefixLift 5792497
  have htrace : WordTrace (prefixWord ++ tailWord_5792497) baseStart_5792497 baseEnd_5792497 := by
    simpa [prefixWord, tailWord_5792497, baseEnd_5792497] using wordTrace_append hprefix tailTrace_5792497
  have hstable : (prefixWord ++ tailWord_5792497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792497).length < 2 ^ (prefixWord ++ tailWord_5792497).sum := by decide
  have hdescent : baseEnd_5792497 < baseStart_5792497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792498 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_5792498 : Nat := 118140960795 + 5792498 * 2 ^ 59
def prefixEnd_5792498 : Nat := 4983230072969 + 3 ^ 40 * 5792498 * 2
def baseEnd_5792498 : Nat := 2974335664207383058635793

theorem tailTrace_5792498 : CollatzResearch.WordTrace tailWord_5792498 prefixEnd_5792498 2974335664207383058635793 := by
  unfold tailWord_5792498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52817439642194125185728537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140846505712517667161942765 52817439642194125185728537)
  ·
    refine ⟨39613079731645593889296403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52817439642194125185728537 39613079731645593889296403)
    ·
      refine ⟨59419619597468390833944605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39613079731645593889296403 59419619597468390833944605)
      ·
        refine ⟨22282357349050646562729227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59419619597468390833944605 22282357349050646562729227)
        ·
          refine ⟨33423536023575969844093841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22282357349050646562729227 33423536023575969844093841)
          ·
            refine ⟨25067652017681977383070381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33423536023575969844093841 25067652017681977383070381)
            ·
              refine ⟨9400369506630741518651393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25067652017681977383070381 9400369506630741518651393)
              ·
                refine ⟨7050277129973056138988545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9400369506630741518651393 7050277129973056138988545)
                ·
                  refine ⟨5287707847479792104241409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7050277129973056138988545 5287707847479792104241409)
                  ·
                    refine ⟨3965780885609844078181057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5287707847479792104241409 3965780885609844078181057)
                    ·
                      refine ⟨2974335664207383058635793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965780885609844078181057 2974335664207383058635793)
                      ·
                        rfl

theorem cell23_5792498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_5792498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792498 prefixEnd_5792498 := by exact prefixLift 5792498
  have htrace : WordTrace (prefixWord ++ tailWord_5792498) baseStart_5792498 baseEnd_5792498 := by
    simpa [prefixWord, tailWord_5792498, baseEnd_5792498] using wordTrace_append hprefix tailTrace_5792498
  have hstable : (prefixWord ++ tailWord_5792498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792498).length < 2 ^ (prefixWord ++ tailWord_5792498).sum := by decide
  have hdescent : baseEnd_5792498 < baseStart_5792498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792615 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5792615 : Nat := 118140960795 + 5792615 * 2 ^ 59
def prefixEnd_5792615 : Nat := 4983230072969 + 3 ^ 40 * 5792615 * 2
def baseEnd_5792615 : Nat := 991465247147986366957585

theorem tailTrace_5792615 : CollatzResearch.WordTrace tailWord_5792615 prefixEnd_5792615 991465247147986366957585 := by
  unfold tailWord_5792615
  simp only [CollatzResearch.WordTrace]
  refine ⟨211274025909352629724923299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140849350606235086483282199 211274025909352629724923299)
  ·
    refine ⟨316911038864028944587384949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211274025909352629724923299 316911038864028944587384949)
    ·
      refine ⟨29710409893502713555067339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316911038864028944587384949 29710409893502713555067339)
      ·
        refine ⟨44565614840254070332601009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29710409893502713555067339 44565614840254070332601009)
        ·
          refine ⟨33424211130190552749450757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44565614840254070332601009 33424211130190552749450757)
          ·
            refine ⟨6267039586910728640522017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33424211130190552749450757 6267039586910728640522017)
            ·
              refine ⟨4700279690183046480391513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267039586910728640522017 4700279690183046480391513)
              ·
                refine ⟨3525209767637284860293635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700279690183046480391513 3525209767637284860293635)
                ·
                  refine ⟨5287814651455927290440453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525209767637284860293635 5287814651455927290440453)
                  ·
                    refine ⟨991465247147986366957585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287814651455927290440453 991465247147986366957585)
                    ·
                      rfl

theorem cell23_5792615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5792615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792615 prefixEnd_5792615 := by exact prefixLift 5792615
  have htrace : WordTrace (prefixWord ++ tailWord_5792615) baseStart_5792615 baseEnd_5792615 := by
    simpa [prefixWord, tailWord_5792615, baseEnd_5792615] using wordTrace_append hprefix tailTrace_5792615
  have hstable : (prefixWord ++ tailWord_5792615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792615).length < 2 ^ (prefixWord ++ tailWord_5792615).sum := by decide
  have hdescent : baseEnd_5792615 < baseStart_5792615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792621 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_5792621 : Nat := 118140960795 + 5792621 * 2 ^ 59
def prefixEnd_5792621 : Nat := 4983230072969 + 3 ^ 40 * 5792621 * 2
def baseEnd_5792621 : Nat := 2974398822327886077397727

theorem tailTrace_5792621 : CollatzResearch.WordTrace tailWord_5792621 prefixEnd_5792621 2974398822327886077397727 := by
  unfold tailWord_5792621
  simp only [CollatzResearch.WordTrace]
  refine ⟨211274244747330892749641717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140849496498220595166427811 211274244747330892749641717)
  ·
    refine ⟨19806960445062271195278911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211274244747330892749641717 19806960445062271195278911)
    ·
      refine ⟨29710440667593406792918367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19806960445062271195278911 29710440667593406792918367)
      ·
        refine ⟨44565661001390110189377551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29710440667593406792918367 44565661001390110189377551)
        ·
          refine ⟨66848491502085165284066327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44565661001390110189377551 66848491502085165284066327)
          ·
            refine ⟨100272737253127747926099491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66848491502085165284066327 100272737253127747926099491)
            ·
              refine ⟨150409105879691621889149237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100272737253127747926099491 150409105879691621889149237)
              ·
                refine ⟨14100853676221089552107741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150409105879691621889149237 14100853676221089552107741)
                ·
                  refine ⟨5287820128582908582040403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14100853676221089552107741 5287820128582908582040403)
                  ·
                    refine ⟨7931730192874362873060605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287820128582908582040403 7931730192874362873060605)
                    ·
                      refine ⟨2974398822327886077397727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931730192874362873060605 2974398822327886077397727)
                      ·
                        rfl

theorem cell23_5792621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_5792621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792621 prefixEnd_5792621 := by exact prefixLift 5792621
  have htrace : WordTrace (prefixWord ++ tailWord_5792621) baseStart_5792621 baseEnd_5792621 := by
    simpa [prefixWord, tailWord_5792621, baseEnd_5792621] using wordTrace_append hprefix tailTrace_5792621
  have hstable : (prefixWord ++ tailWord_5792621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792621).length < 2 ^ (prefixWord ++ tailWord_5792621).sum := by decide
  have hdescent : baseEnd_5792621 < baseStart_5792621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792642 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5792642 : Nat := 118140960795 + 5792642 * 2 ^ 59
def prefixEnd_5792642 : Nat := 4983230072969 + 3 ^ 40 * 5792642 * 2
def baseEnd_5792642 : Nat := 2974409605421630495235131

theorem tailTrace_5792642 : CollatzResearch.WordTrace tailWord_5792642 prefixEnd_5792642 2974409605421630495235131 := by
  unfold tailWord_5792642
  simp only [CollatzResearch.WordTrace]
  refine ⟨52818752670063703334039045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140850007120169875557437453 52818752670063703334039045)
  ·
    refine ⟨9903516125636944375132321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52818752670063703334039045 9903516125636944375132321)
    ·
      refine ⟨7427637094227708281349241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9903516125636944375132321 7427637094227708281349241)
      ·
        refine ⟨5570727820670781211011931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7427637094227708281349241 5570727820670781211011931)
        ·
          refine ⟨8356091731006171816517897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570727820670781211011931 8356091731006171816517897)
          ·
            refine ⟨6267068798254628862388423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8356091731006171816517897 6267068798254628862388423)
            ·
              refine ⟨9400603197381943293582635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267068798254628862388423 9400603197381943293582635)
              ·
                refine ⟨14100904796072914940373953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9400603197381943293582635 14100904796072914940373953)
                ·
                  refine ⟨10575678597054686205280465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14100904796072914940373953 10575678597054686205280465)
                  ·
                    refine ⟨7931758947791014653960349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10575678597054686205280465 7931758947791014653960349)
                    ·
                      refine ⟨2974409605421630495235131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931758947791014653960349 2974409605421630495235131)
                      ·
                        rfl

theorem cell23_5792642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5792642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792642 prefixEnd_5792642 := by exact prefixLift 5792642
  have htrace : WordTrace (prefixWord ++ tailWord_5792642) baseStart_5792642 baseEnd_5792642 := by
    simpa [prefixWord, tailWord_5792642, baseEnd_5792642] using wordTrace_append hprefix tailTrace_5792642
  have hstable : (prefixWord ++ tailWord_5792642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792642).length < 2 ^ (prefixWord ++ tailWord_5792642).sum := by decide
  have hdescent : baseEnd_5792642 < baseStart_5792642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792648 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5792648 : Nat := 118140960795 + 5792648 * 2 ^ 59
def prefixEnd_5792648 : Nat := 4983230072969 + 3 ^ 40 * 5792648 * 2
def baseEnd_5792648 : Nat := 2974412686305557471760103

theorem tailTrace_5792648 : CollatzResearch.WordTrace tailWord_5792648 prefixEnd_5792648 2974412686305557471760103 := by
  unfold tailWord_5792648
  simp only [CollatzResearch.WordTrace]
  refine ⟨105637614759116538180437299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140850153012155384240583065 105637614759116538180437299)
  ·
    refine ⟨158456422138674807270655949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105637614759116538180437299 158456422138674807270655949)
    ·
      refine ⟨59421158302003052726495981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158456422138674807270655949 59421158302003052726495981)
      ·
        refine ⟨22282934363251144772435993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59421158302003052726495981 22282934363251144772435993)
        ·
          refine ⟨16712200772438358579326995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22282934363251144772435993 16712200772438358579326995)
          ·
            refine ⟨25068301158657537868990493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712200772438358579326995 25068301158657537868990493)
            ·
              refine ⟨9400612934496576700871435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25068301158657537868990493 9400612934496576700871435)
              ·
                refine ⟨14100919401744865051307153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9400612934496576700871435 14100919401744865051307153)
                ·
                  refine ⟨10575689551308648788480365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14100919401744865051307153 10575689551308648788480365)
                  ·
                    refine ⟨3965883581740743295680137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10575689551308648788480365 3965883581740743295680137)
                    ·
                      refine ⟨2974412686305557471760103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965883581740743295680137 2974412686305557471760103)
                      ·
                        rfl

theorem cell23_5792648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5792648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792648 prefixEnd_5792648 := by exact prefixLift 5792648
  have htrace : WordTrace (prefixWord ++ tailWord_5792648) baseStart_5792648 baseEnd_5792648 := by
    simpa [prefixWord, tailWord_5792648, baseEnd_5792648] using wordTrace_append hprefix tailTrace_5792648
  have hstable : (prefixWord ++ tailWord_5792648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792648).length < 2 ^ (prefixWord ++ tailWord_5792648).sum := by decide
  have hdescent : baseEnd_5792648 < baseStart_5792648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792657 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_5792657 : Nat := 118140960795 + 5792657 * 2 ^ 59
def prefixEnd_5792657 : Nat := 4983230072969 + 3 ^ 40 * 5792657 * 2
def baseEnd_5792657 : Nat := 2974417307631447936547561

theorem tailTrace_5792657 : CollatzResearch.WordTrace tailWord_5792657 prefixEnd_5792657 2974417307631447936547561 := by
  unfold tailWord_5792657
  simp only [CollatzResearch.WordTrace]
  refine ⟨211275557775200470897952225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140850371850133647265301483 211275557775200470897952225)
  ·
    refine ⟨158456668331400353173464169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211275557775200470897952225 158456668331400353173464169)
    ·
      refine ⟨118842501248550264880098127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158456668331400353173464169 118842501248550264880098127)
      ·
        refine ⟨178263751872825397320147191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118842501248550264880098127 178263751872825397320147191)
        ·
          refine ⟨267395627809238095980220787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178263751872825397320147191 267395627809238095980220787)
          ·
            refine ⟨401093441713857143970331181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267395627809238095980220787 401093441713857143970331181)
            ·
              refine ⟨150410040642696428988874193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401093441713857143970331181 150410040642696428988874193)
              ·
                refine ⟨112807530482022321741655645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150410040642696428988874193 112807530482022321741655645)
                ·
                  refine ⟨42302823930758370653120867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112807530482022321741655645 42302823930758370653120867)
                  ·
                    refine ⟨63454235896137555979681301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42302823930758370653120867 63454235896137555979681301)
                    ·
                      refine ⟨2974417307631447936547561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63454235896137555979681301 2974417307631447936547561)
                      ·
                        rfl

theorem cell23_5792657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_5792657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792657 prefixEnd_5792657 := by exact prefixLift 5792657
  have htrace : WordTrace (prefixWord ++ tailWord_5792657) baseStart_5792657 baseEnd_5792657 := by
    simpa [prefixWord, tailWord_5792657, baseEnd_5792657] using wordTrace_append hprefix tailTrace_5792657
  have hstable : (prefixWord ++ tailWord_5792657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792657).length < 2 ^ (prefixWord ++ tailWord_5792657).sum := by decide
  have hdescent : baseEnd_5792657 < baseStart_5792657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792658 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_5792658 : Nat := 118140960795 + 5792658 * 2 ^ 59
def prefixEnd_5792658 : Nat := 4983230072969 + 3 ^ 40 * 5792658 * 2
def baseEnd_5792658 : Nat := 991472607037367477545019

theorem tailTrace_5792658 : CollatzResearch.WordTrace tailWord_5792658 prefixEnd_5792658 991472607037367477545019 := by
  unfold tailWord_5792658
  simp only [CollatzResearch.WordTrace]
  refine ⟨52818898562049212017184657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140850396165464565379159085 52818898562049212017184657)
  ·
    refine ⟨39614173921536909012888493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52818898562049212017184657 39614173921536909012888493)
    ·
      refine ⟨14855315220576340879833185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39614173921536909012888493 14855315220576340879833185)
      ·
        refine ⟨11141486415432255659874889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14855315220576340879833185 11141486415432255659874889)
        ·
          refine ⟨8356114811574191744906167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11141486415432255659874889 8356114811574191744906167)
          ·
            refine ⟨12534172217361287617359251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356114811574191744906167 12534172217361287617359251)
            ·
              refine ⟨18801258326041931426038877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12534172217361287617359251 18801258326041931426038877)
              ·
                refine ⟨7050471872265724284764579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18801258326041931426038877 7050471872265724284764579)
                ·
                  refine ⟨10575707808398586427146869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050471872265724284764579 10575707808398586427146869)
                  ·
                    refine ⟨991472607037367477545019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10575707808398586427146869 991472607037367477545019)
                    ·
                      rfl

theorem cell23_5792658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_5792658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792658 prefixEnd_5792658 := by exact prefixLift 5792658
  have htrace : WordTrace (prefixWord ++ tailWord_5792658) baseStart_5792658 baseEnd_5792658 := by
    simpa [prefixWord, tailWord_5792658, baseEnd_5792658] using wordTrace_append hprefix tailTrace_5792658
  have hstable : (prefixWord ++ tailWord_5792658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792658).length < 2 ^ (prefixWord ++ tailWord_5792658).sum := by decide
  have hdescent : baseEnd_5792658 < baseStart_5792658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792661 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_5792661 : Nat := 118140960795 + 5792661 * 2 ^ 59
def prefixEnd_5792661 : Nat := 4983230072969 + 3 ^ 40 * 5792661 * 2
def baseEnd_5792661 : Nat := 2974419361554065920897543

theorem tailTrace_5792661 : CollatzResearch.WordTrace tailWord_5792661 prefixEnd_5792661 2974419361554065920897543 := by
  unfold tailWord_5792661
  simp only [CollatzResearch.WordTrace]
  refine ⟨211275703667185979581097837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140850469111457319720731891 211275703667185979581097837)
  ·
    refine ⟨79228388875194742342911689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211275703667185979581097837 79228388875194742342911689)
    ·
      refine ⟨59421291656396056757183767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79228388875194742342911689 59421291656396056757183767)
      ·
        refine ⟨89131937484594085135775651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59421291656396056757183767 89131937484594085135775651)
        ·
          refine ⟨133697906226891127703663477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89131937484594085135775651 133697906226891127703663477)
          ·
            refine ⟨12534178708771043222218451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133697906226891127703663477 12534178708771043222218451)
            ·
              refine ⟨18801268063156564833327677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12534178708771043222218451 18801268063156564833327677)
              ·
                refine ⟨7050475523683711812497879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18801268063156564833327677 7050475523683711812497879)
                ·
                  refine ⟨10575713285525567718746819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050475523683711812497879 10575713285525567718746819)
                  ·
                    refine ⟨15863569928288351578120229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10575713285525567718746819 15863569928288351578120229)
                    ·
                      refine ⟨2974419361554065920897543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15863569928288351578120229 2974419361554065920897543)
                      ·
                        rfl

theorem cell23_5792661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_5792661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792661 prefixEnd_5792661 := by exact prefixLift 5792661
  have htrace : WordTrace (prefixWord ++ tailWord_5792661) baseStart_5792661 baseEnd_5792661 := by
    simpa [prefixWord, tailWord_5792661, baseEnd_5792661] using wordTrace_append hprefix tailTrace_5792661
  have hstable : (prefixWord ++ tailWord_5792661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792661).length < 2 ^ (prefixWord ++ tailWord_5792661).sum := by decide
  have hdescent : baseEnd_5792661 < baseStart_5792661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792671 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 4, 4]
def baseStart_5792671 : Nat := 118140960795 + 5792671 * 2 ^ 59
def prefixEnd_5792671 : Nat := 4983230072969 + 3 ^ 40 * 5792671 * 2
def baseEnd_5792671 : Nat := 991474832120203627257499

theorem tailTrace_5792671 : CollatzResearch.WordTrace tailWord_5792671 prefixEnd_5792671 991474832120203627257499 := by
  unfold tailWord_5792671
  simp only [CollatzResearch.WordTrace]
  refine ⟨211276068397149751288961867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140850712264766500859307911 211276068397149751288961867)
  ·
    refine ⟨316914102595724626933442801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211276068397149751288961867 316914102595724626933442801)
    ·
      refine ⟨237685576946793470200082101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316914102595724626933442801 237685576946793470200082101)
      ·
        refine ⟨22283022838761887831257697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237685576946793470200082101 22283022838761887831257697)
        ·
          refine ⟨16712267129071415873443273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22283022838761887831257697 16712267129071415873443273)
          ·
            refine ⟨12534200346803561905082455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16712267129071415873443273 12534200346803561905082455)
            ·
              refine ⟨18801300520205342857623683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12534200346803561905082455 18801300520205342857623683)
              ·
                refine ⟨28201950780308014286435525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18801300520205342857623683 28201950780308014286435525)
                ·
                  refine ⟨5287865771307752678706661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28201950780308014286435525 5287865771307752678706661)
                  ·
                    refine ⟨991474832120203627257499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5287865771307752678706661 991474832120203627257499)
                    ·
                      rfl

theorem cell23_5792671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_5792671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792671 prefixEnd_5792671 := by exact prefixLift 5792671
  have htrace : WordTrace (prefixWord ++ tailWord_5792671) baseStart_5792671 baseEnd_5792671 := by
    simpa [prefixWord, tailWord_5792671, baseEnd_5792671] using wordTrace_append hprefix tailTrace_5792671
  have hstable : (prefixWord ++ tailWord_5792671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792671).length < 2 ^ (prefixWord ++ tailWord_5792671).sum := by decide
  have hdescent : baseEnd_5792671 < baseStart_5792671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792677 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_5792677 : Nat := 118140960795 + 5792677 * 2 ^ 59
def prefixEnd_5792677 : Nat := 4983230072969 + 3 ^ 40 * 5792677 * 2
def baseEnd_5792677 : Nat := 2974427577244537858297469

theorem tailTrace_5792677 : CollatzResearch.WordTrace tailWord_5792677 prefixEnd_5792677 2974427577244537858297469 := by
  unfold tailWord_5792677
  simp only [CollatzResearch.WordTrace]
  refine ⟨211276287235128014313680285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140850858156752009542453523 211276287235128014313680285)
  ·
    refine ⟨79228607713173005367630107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211276287235128014313680285 79228607713173005367630107)
    ·
      refine ⟨118842911569759508051445161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79228607713173005367630107 118842911569759508051445161)
      ·
        refine ⟨89132183677319631038583871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118842911569759508051445161 89132183677319631038583871)
        ·
          refine ⟨133698275515979446557875807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89132183677319631038583871 133698275515979446557875807)
          ·
            refine ⟨200547413273969169836813711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133698275515979446557875807 200547413273969169836813711)
            ·
              refine ⟨300821119910953754755220567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200547413273969169836813711 300821119910953754755220567)
              ·
                refine ⟨451231679866430632132830851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300821119910953754755220567 451231679866430632132830851)
                ·
                  refine ⟨676847519799645948199246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451231679866430632132830851 676847519799645948199246277)
                  ·
                    refine ⟨126908909962433615287358677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676847519799645948199246277 126908909962433615287358677)
                    ·
                      refine ⟨2974427577244537858297469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126908909962433615287358677 2974427577244537858297469)
                      ·
                        rfl

theorem cell23_5792677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_5792677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792677 prefixEnd_5792677 := by exact prefixLift 5792677
  have htrace : WordTrace (prefixWord ++ tailWord_5792677) baseStart_5792677 baseEnd_5792677 := by
    simpa [prefixWord, tailWord_5792677, baseEnd_5792677] using wordTrace_append hprefix tailTrace_5792677
  have hstable : (prefixWord ++ tailWord_5792677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792677).length < 2 ^ (prefixWord ++ tailWord_5792677).sum := by decide
  have hdescent : baseEnd_5792677 < baseStart_5792677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792687 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_5792687 : Nat := 118140960795 + 5792687 * 2 ^ 59
def prefixEnd_5792687 : Nat := 4983230072969 + 3 ^ 40 * 5792687 * 2
def baseEnd_5792687 : Nat := 2974432712051082819172423

theorem tailTrace_5792687 : CollatzResearch.WordTrace tailWord_5792687 prefixEnd_5792687 2974432712051082819172423 := by
  unfold tailWord_5792687
  simp only [CollatzResearch.WordTrace]
  refine ⟨211276651965091786021544315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140851101310061190681029543 211276651965091786021544315)
  ·
    refine ⟨316914977947637679032316473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211276651965091786021544315 316914977947637679032316473)
    ·
      refine ⟨237686233460728259274237355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316914977947637679032316473 237686233460728259274237355)
      ·
        refine ⟨356529350191092388911356033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237686233460728259274237355 356529350191092388911356033)
        ·
          refine ⟨267397012643319291683517025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356529350191092388911356033 267397012643319291683517025)
          ·
            refine ⟨200547759482489468762637769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267397012643319291683517025 200547759482489468762637769)
            ·
              refine ⟨150410819611867101571978327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200547759482489468762637769 150410819611867101571978327)
              ·
                refine ⟨225616229417800652357967491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150410819611867101571978327 225616229417800652357967491)
                ·
                  refine ⟨338424344126700978536951237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225616229417800652357967491 338424344126700978536951237)
                  ·
                    refine ⟨63454564523756433475678357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338424344126700978536951237 63454564523756433475678357)
                    ·
                      refine ⟨2974432712051082819172423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63454564523756433475678357 2974432712051082819172423)
                      ·
                        rfl

theorem cell23_5792687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_5792687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792687 prefixEnd_5792687 := by exact prefixLift 5792687
  have htrace : WordTrace (prefixWord ++ tailWord_5792687) baseStart_5792687 baseEnd_5792687 := by
    simpa [prefixWord, tailWord_5792687, baseEnd_5792687] using wordTrace_append hprefix tailTrace_5792687
  have hstable : (prefixWord ++ tailWord_5792687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792687).length < 2 ^ (prefixWord ++ tailWord_5792687).sum := by decide
  have hdescent : baseEnd_5792687 < baseStart_5792687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792711 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_5792711 : Nat := 118140960795 + 5792711 * 2 ^ 59
def prefixEnd_5792711 : Nat := 4983230072969 + 3 ^ 40 * 5792711 * 2
def baseEnd_5792711 : Nat := 2974445035586790725272313

theorem tailTrace_5792711 : CollatzResearch.WordTrace tailWord_5792711 prefixEnd_5792711 2974445035586790725272313 := by
  unfold tailWord_5792711
  simp only [CollatzResearch.WordTrace]
  refine ⟨211277527317004838120417987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140851684878003225413611991 211277527317004838120417987)
  ·
    refine ⟨316916290975507257180626981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211277527317004838120417987 316916290975507257180626981)
    ·
      refine ⟨59421804557907610721367559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316916290975507257180626981 59421804557907610721367559)
      ·
        refine ⟨89132706836861416082051339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59421804557907610721367559 89132706836861416082051339)
        ·
          refine ⟨133699060255292124123077009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89132706836861416082051339 133699060255292124123077009)
          ·
            refine ⟨100274295191469093092307757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133699060255292124123077009 100274295191469093092307757)
            ·
              refine ⟨37602860696800909909615409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100274295191469093092307757 37602860696800909909615409)
              ·
                refine ⟨28202145522600682432211557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37602860696800909909615409 28202145522600682432211557)
                ·
                  refine ⟨5287902285487627956039667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28202145522600682432211557 5287902285487627956039667)
                  ·
                    refine ⟨7931853428231441934059501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287902285487627956039667 7931853428231441934059501)
                    ·
                      refine ⟨2974445035586790725272313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931853428231441934059501 2974445035586790725272313)
                      ·
                        rfl

theorem cell23_5792711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_5792711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792711 prefixEnd_5792711 := by exact prefixLift 5792711
  have htrace : WordTrace (prefixWord ++ tailWord_5792711) baseStart_5792711 baseEnd_5792711 := by
    simpa [prefixWord, tailWord_5792711, baseEnd_5792711] using wordTrace_append hprefix tailTrace_5792711
  have hstable : (prefixWord ++ tailWord_5792711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792711).length < 2 ^ (prefixWord ++ tailWord_5792711).sum := by decide
  have hdescent : baseEnd_5792711 < baseStart_5792711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792744 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5792744 : Nat := 118140960795 + 5792744 * 2 ^ 59
def prefixEnd_5792744 : Nat := 4983230072969 + 3 ^ 40 * 5792744 * 2
def baseEnd_5792744 : Nat := 991487326816129698719887

theorem tailTrace_5792744 : CollatzResearch.WordTrace tailWord_5792744 prefixEnd_5792744 991487326816129698719887 := by
  unfold tailWord_5792744
  simp only [CollatzResearch.WordTrace]
  refine ⟨105639365462942642378184643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140852487283923523170912857 105639365462942642378184643)
  ·
    refine ⟨158459048194413963567276965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105639365462942642378184643 158459048194413963567276965)
    ·
      refine ⟨29711071536452618168864431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158459048194413963567276965 29711071536452618168864431)
      ·
        refine ⟨44566607304678927253296647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29711071536452618168864431 44566607304678927253296647)
        ·
          refine ⟨66849910957018390879944971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44566607304678927253296647 66849910957018390879944971)
          ·
            refine ⟨100274866435527586319917457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66849910957018390879944971 100274866435527586319917457)
            ·
              refine ⟨75206149826645689739938093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100274866435527586319917457 75206149826645689739938093)
              ·
                refine ⟨28202306184992133652476785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75206149826645689739938093 28202306184992133652476785)
                ·
                  refine ⟨21151729638744100239357589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28202306184992133652476785 21151729638744100239357589)
                  ·
                    refine ⟨991487326816129698719887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21151729638744100239357589 991487326816129698719887)
                    ·
                      rfl

theorem cell23_5792744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5792744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792744 prefixEnd_5792744 := by exact prefixLift 5792744
  have htrace : WordTrace (prefixWord ++ tailWord_5792744) baseStart_5792744 baseEnd_5792744 := by
    simpa [prefixWord, tailWord_5792744, baseEnd_5792744] using wordTrace_append hprefix tailTrace_5792744
  have hstable : (prefixWord ++ tailWord_5792744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792744).length < 2 ^ (prefixWord ++ tailWord_5792744).sum := by decide
  have hdescent : baseEnd_5792744 < baseStart_5792744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792801 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5792801 : Nat := 118140960795 + 5792801 * 2 ^ 59
def prefixEnd_5792801 : Nat := 4983230072969 + 3 ^ 40 * 5792801 * 2
def baseEnd_5792801 : Nat := 2974491248845695373146899

theorem tailTrace_5792801 : CollatzResearch.WordTrace tailWord_5792801 prefixEnd_5792801 2974491248845695373146899 := by
  unfold tailWord_5792801
  simp only [CollatzResearch.WordTrace]
  refine ⟨211280809886678783491194257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140853873257785855660796171 211280809886678783491194257)
  ·
    refine ⟨158460607415009087618395693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211280809886678783491194257 158460607415009087618395693)
    ·
      refine ⟨59422727780628407856898385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158460607415009087618395693 59422727780628407856898385)
      ·
        refine ⟨44567045835471305892673789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59422727780628407856898385 44567045835471305892673789)
        ·
          refine ⟨16712642188301739709752671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44567045835471305892673789 16712642188301739709752671)
          ·
            refine ⟨25068963282452609564629007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712642188301739709752671 25068963282452609564629007)
            ·
              refine ⟨37603444923678914346943511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25068963282452609564629007 37603444923678914346943511)
              ·
                refine ⟨56405167385518371520415267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37603444923678914346943511 56405167385518371520415267)
                ·
                  refine ⟨84607751078277557280622901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56405167385518371520415267 84607751078277557280622901)
                  ·
                    refine ⟨7931976663588520995058397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84607751078277557280622901 7931976663588520995058397)
                    ·
                      refine ⟨2974491248845695373146899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7931976663588520995058397 2974491248845695373146899)
                      ·
                        rfl

theorem cell23_5792801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5792801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792801 prefixEnd_5792801 := by exact prefixLift 5792801
  have htrace : WordTrace (prefixWord ++ tailWord_5792801) baseStart_5792801 baseEnd_5792801 := by
    simpa [prefixWord, tailWord_5792801, baseEnd_5792801] using wordTrace_append hprefix tailTrace_5792801
  have hstable : (prefixWord ++ tailWord_5792801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792801).length < 2 ^ (prefixWord ++ tailWord_5792801).sum := by decide
  have hdescent : baseEnd_5792801 < baseStart_5792801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792811 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 5, 2]
def baseStart_5792811 : Nat := 118140960795 + 5792811 * 2 ^ 59
def prefixEnd_5792811 : Nat := 4983230072969 + 3 ^ 40 * 5792811 * 2
def baseEnd_5792811 : Nat := 2974496383652240334021853

theorem tailTrace_5792811 : CollatzResearch.WordTrace tailWord_5792811 prefixEnd_5792811 2974496383652240334021853 := by
  unfold tailWord_5792811
  simp only [CollatzResearch.WordTrace]
  refine ⟨211281174616642555199058287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140854116411095036799372191 211281174616642555199058287)
  ·
    refine ⟨316921761924963832798587431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211281174616642555199058287 316921761924963832798587431)
    ·
      refine ⟨475382642887445749197881147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316921761924963832798587431 475382642887445749197881147)
      ·
        refine ⟨713073964331168623796821721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475382642887445749197881147 713073964331168623796821721)
        ·
          refine ⟨534805473248376467847616291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713073964331168623796821721 534805473248376467847616291)
          ·
            refine ⟨802208209872564701771424437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534805473248376467847616291 802208209872564701771424437)
            ·
              refine ⟨75207019675552940791071041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 802208209872564701771424437 75207019675552940791071041)
              ·
                refine ⟨56405264756664705593303281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75207019675552940791071041 56405264756664705593303281)
                ·
                  refine ⟨42303948567498529194977461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56405264756664705593303281 42303948567498529194977461)
                  ·
                    refine ⟨3965995178202987112029137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42303948567498529194977461 3965995178202987112029137)
                    ·
                      refine ⟨2974496383652240334021853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3965995178202987112029137 2974496383652240334021853)
                      ·
                        rfl

theorem cell23_5792811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 5, 2].length) (baseStart_5792811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792811 prefixEnd_5792811 := by exact prefixLift 5792811
  have htrace : WordTrace (prefixWord ++ tailWord_5792811) baseStart_5792811 baseEnd_5792811 := by
    simpa [prefixWord, tailWord_5792811, baseEnd_5792811] using wordTrace_append hprefix tailTrace_5792811
  have hstable : (prefixWord ++ tailWord_5792811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792811).length < 2 ^ (prefixWord ++ tailWord_5792811).sum := by decide
  have hdescent : baseEnd_5792811 < baseStart_5792811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792851 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 3, 4]
def baseStart_5792851 : Nat := 118140960795 + 5792851 * 2 ^ 59
def prefixEnd_5792851 : Nat := 4983230072969 + 3 ^ 40 * 5792851 * 2
def baseEnd_5792851 : Nat := 991505640959473392507223

theorem tailTrace_5792851 : CollatzResearch.WordTrace tailWord_5792851 prefixEnd_5792851 991505640959473392507223 := by
  unfold tailWord_5792851
  simp only [CollatzResearch.WordTrace]
  refine ⟨211282633536497642030514407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140855089024331761353676271 211282633536497642030514407)
  ·
    refine ⟨316923950304746463045771611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211282633536497642030514407 316923950304746463045771611)
    ·
      refine ⟨475385925457119694568657417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316923950304746463045771611 475385925457119694568657417)
      ·
        refine ⟨356539444092839770926493063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475385925457119694568657417 356539444092839770926493063)
        ·
          refine ⟨534809166139259656389739595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356539444092839770926493063 534809166139259656389739595)
          ·
            refine ⟨802213749208889484584609393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534809166139259656389739595 802213749208889484584609393)
            ·
              refine ⟨601660311906667113438457045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802213749208889484584609393 601660311906667113438457045)
              ·
                refine ⟨14101413560312510471213837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 601660311906667113438457045 14101413560312510471213837)
                ·
                  refine ⟨5288030085117191426705189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14101413560312510471213837 5288030085117191426705189)
                  ·
                    refine ⟨991505640959473392507223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288030085117191426705189 991505640959473392507223)
                    ·
                      rfl

theorem cell23_5792851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 4].length) (baseStart_5792851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792851 prefixEnd_5792851 := by exact prefixLift 5792851
  have htrace : WordTrace (prefixWord ++ tailWord_5792851) baseStart_5792851 baseEnd_5792851 := by
    simpa [prefixWord, tailWord_5792851, baseEnd_5792851] using wordTrace_append hprefix tailTrace_5792851
  have hstable : (prefixWord ++ tailWord_5792851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792851).length < 2 ^ (prefixWord ++ tailWord_5792851).sum := by decide
  have hdescent : baseEnd_5792851 < baseStart_5792851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792878 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5792878 : Nat := 118140960795 + 5792878 * 2 ^ 59
def prefixEnd_5792878 : Nat := 4983230072969 + 3 ^ 40 * 5792878 * 2
def baseEnd_5792878 : Nat := 2974530786856091571884045

theorem tailTrace_5792878 : CollatzResearch.WordTrace tailWord_5792878 prefixEnd_5792878 2974530786856091571884045 := by
  unfold tailWord_5792878
  simp only [CollatzResearch.WordTrace]
  refine ⟨26410452288424978205218411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140855745538266550427831525 26410452288424978205218411)
  ·
    refine ⟨39615678432637467307827617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26410452288424978205218411 39615678432637467307827617)
    ·
      refine ⟨29711758824478100480870713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39615678432637467307827617 29711758824478100480870713)
      ·
        refine ⟨22283819118358575360653035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29711758824478100480870713 22283819118358575360653035)
        ·
          refine ⟨33425728677537863040979553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22283819118358575360653035 33425728677537863040979553)
          ·
            refine ⟨25069296508153397280734665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33425728677537863040979553 25069296508153397280734665)
            ·
              refine ⟨18801972381115047960550999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25069296508153397280734665 18801972381115047960550999)
              ·
                refine ⟨28202958571672571940826499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18801972381115047960550999 28202958571672571940826499)
                ·
                  refine ⟨42304437857508857911239749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28202958571672571940826499 42304437857508857911239749)
                  ·
                    refine ⟨7932082098282910858357453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42304437857508857911239749 7932082098282910858357453)
                    ·
                      refine ⟨2974530786856091571884045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932082098282910858357453 2974530786856091571884045)
                      ·
                        rfl

theorem cell23_5792878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5792878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792878 prefixEnd_5792878 := by exact prefixLift 5792878
  have htrace : WordTrace (prefixWord ++ tailWord_5792878) baseStart_5792878 baseEnd_5792878 := by
    simpa [prefixWord, tailWord_5792878, baseEnd_5792878] using wordTrace_append hprefix tailTrace_5792878
  have hstable : (prefixWord ++ tailWord_5792878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792878).length < 2 ^ (prefixWord ++ tailWord_5792878).sum := by decide
  have hdescent : baseEnd_5792878 < baseStart_5792878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792965 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_5792965 : Nat := 118140960795 + 5792965 * 2 ^ 59
def prefixEnd_5792965 : Nat := 4983230072969 + 3 ^ 40 * 5792965 * 2
def baseEnd_5792965 : Nat := 2974575459673032731496145

theorem tailTrace_5792965 : CollatzResearch.WordTrace tailWord_5792965 prefixEnd_5792965 2974575459673032731496145 := by
  unfold tailWord_5792965
  simp only [CollatzResearch.WordTrace]
  refine ⟨211286791458084639500164349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140857860972056426333442899 211286791458084639500164349)
  ·
    refine ⟨79232546796781739812561631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211286791458084639500164349 79232546796781739812561631)
    ·
      refine ⟨118848820195172609718842447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79232546796781739812561631 118848820195172609718842447)
      ·
        refine ⟨178273230292758914578263671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118848820195172609718842447 178273230292758914578263671)
        ·
          refine ⟨267409845439138371867395507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178273230292758914578263671 267409845439138371867395507)
          ·
            refine ⟨401114768158707557801093261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267409845439138371867395507 401114768158707557801093261)
            ·
              refine ⟨150418038059515334175409973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401114768158707557801093261 150418038059515334175409973)
              ·
                refine ⟨14101691068079562578944685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150418038059515334175409973 14101691068079562578944685)
                ·
                  refine ⟨5288134150529835967104257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14101691068079562578944685 5288134150529835967104257)
                  ·
                    refine ⟨3966100612897376975328193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5288134150529835967104257 3966100612897376975328193)
                    ·
                      refine ⟨2974575459673032731496145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966100612897376975328193 2974575459673032731496145)
                      ·
                        rfl

theorem cell23_5792965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_5792965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792965 prefixEnd_5792965 := by exact prefixLift 5792965
  have htrace : WordTrace (prefixWord ++ tailWord_5792965) baseStart_5792965 baseEnd_5792965 := by
    simpa [prefixWord, tailWord_5792965, baseEnd_5792965] using wordTrace_append hprefix tailTrace_5792965
  have hstable : (prefixWord ++ tailWord_5792965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792965).length < 2 ^ (prefixWord ++ tailWord_5792965).sum := by decide
  have hdescent : baseEnd_5792965 < baseStart_5792965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792968 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_5792968 : Nat := 118140960795 + 5792968 * 2 ^ 59
def prefixEnd_5792968 : Nat := 4983230072969 + 3 ^ 40 * 5792968 * 2
def baseEnd_5792968 : Nat := 2974577000114996219758631

theorem tailTrace_5792968 : CollatzResearch.WordTrace tailWord_5792968 prefixEnd_5792968 2974577000114996219758631 := by
  unfold tailWord_5792968
  simp only [CollatzResearch.WordTrace]
  refine ⟨105643450438536885506261779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140857933918049180675015705 105643450438536885506261779)
  ·
    refine ⟨158465175657805328259392669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105643450438536885506261779 158465175657805328259392669)
    ·
      refine ⟨59424440871676998097272251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158465175657805328259392669 59424440871676998097272251)
      ·
        refine ⟨89136661307515497145908377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59424440871676998097272251 89136661307515497145908377)
        ·
          refine ⟨66852495980636622859431283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89136661307515497145908377 66852495980636622859431283)
          ·
            refine ⟨100278743970954934289146925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66852495980636622859431283 100278743970954934289146925)
            ·
              refine ⟨37604528989108100358430097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100278743970954934289146925 37604528989108100358430097)
              ·
                refine ⟨28203396741831075268822573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37604528989108100358430097 28203396741831075268822573)
                ·
                  refine ⟨10576273778186653225808465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28203396741831075268822573 10576273778186653225808465)
                  ·
                    refine ⟨7932205333639989919356349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10576273778186653225808465 7932205333639989919356349)
                    ·
                      refine ⟨2974577000114996219758631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932205333639989919356349 2974577000114996219758631)
                      ·
                        rfl

theorem cell23_5792968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_5792968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792968 prefixEnd_5792968 := by exact prefixLift 5792968
  have htrace : WordTrace (prefixWord ++ tailWord_5792968) baseStart_5792968 baseEnd_5792968 := by
    simpa [prefixWord, tailWord_5792968, baseEnd_5792968] using wordTrace_append hprefix tailTrace_5792968
  have hstable : (prefixWord ++ tailWord_5792968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792968).length < 2 ^ (prefixWord ++ tailWord_5792968).sum := by decide
  have hdescent : baseEnd_5792968 < baseStart_5792968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5792999 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5792999 : Nat := 118140960795 + 5792999 * 2 ^ 59
def prefixEnd_5792999 : Nat := 4983230072969 + 3 ^ 40 * 5792999 * 2
def baseEnd_5792999 : Nat := 2974592918015285598470989

theorem tailTrace_5792999 : CollatzResearch.WordTrace tailWord_5792999 prefixEnd_5792999 2974592918015285598470989 := by
  unfold tailWord_5792999
  simp only [CollatzResearch.WordTrace]
  refine ⟨211288031539961463306902051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140858687693307642204601367 211288031539961463306902051)
  ·
    refine ⟨316932047309942194960353077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211288031539961463306902051 316932047309942194960353077)
    ·
      refine ⟨29712379435307080777533101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316932047309942194960353077 29712379435307080777533101)
      ·
        refine ⟨11142142288240155291574913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29712379435307080777533101 11142142288240155291574913)
        ·
          refine ⟨8356606716180116468681185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11142142288240155291574913 8356606716180116468681185)
          ·
            refine ⟨6267455037135087351510889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8356606716180116468681185 6267455037135087351510889)
            ·
              refine ⟨4700591277851315513633167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267455037135087351510889 4700591277851315513633167)
              ·
                refine ⟨7050886916776973270449751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700591277851315513633167 7050886916776973270449751)
                ·
                  refine ⟨10576330375165459905674627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050886916776973270449751 10576330375165459905674627)
                  ·
                    refine ⟨15864495562748189858511941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10576330375165459905674627 15864495562748189858511941)
                    ·
                      refine ⟨2974592918015285598470989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15864495562748189858511941 2974592918015285598470989)
                      ·
                        rfl

theorem cell23_5792999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5792999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5792999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5792999 prefixEnd_5792999 := by exact prefixLift 5792999
  have htrace : WordTrace (prefixWord ++ tailWord_5792999) baseStart_5792999 baseEnd_5792999 := by
    simpa [prefixWord, tailWord_5792999, baseEnd_5792999] using wordTrace_append hprefix tailTrace_5792999
  have hstable : (prefixWord ++ tailWord_5792999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5792999).length < 2 ^ (prefixWord ++ tailWord_5792999).sum := by decide
  have hdescent : baseEnd_5792999 < baseStart_5792999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5792999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793002 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_5793002 : Nat := 118140960795 + 5793002 * 2 ^ 59
def prefixEnd_5793002 : Nat := 4983230072969 + 3 ^ 40 * 5793002 * 2
def baseEnd_5793002 : Nat := 2974594458457249086733475

theorem tailTrace_5793002 : CollatzResearch.WordTrace tailWord_5793002 prefixEnd_5793002 2974594458457249086733475 := by
  unfold tailWord_5793002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52822035239737648704815315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140858760639300396546174173 52822035239737648704815315)
  ·
    refine ⟨79233052859606473057222973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52822035239737648704815315 79233052859606473057222973)
    ·
      refine ⟨29712394822352427396458615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79233052859606473057222973 29712394822352427396458615)
      ·
        refine ⟨44568592233528641094687923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29712394822352427396458615 44568592233528641094687923)
        ·
          refine ⟨66852888350292961642031885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44568592233528641094687923 66852888350292961642031885)
          ·
            refine ⟨25069833131359860615761957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66852888350292961642031885 25069833131359860615761957)
            ·
              refine ⟨4700593712129973865455367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25069833131359860615761957 4700593712129973865455367)
              ·
                refine ⟨7050890568194960798183051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700593712129973865455367 7050890568194960798183051)
                ·
                  refine ⟨10576335852292441197274577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7050890568194960798183051 10576335852292441197274577)
                  ·
                    refine ⟨7932251889219330897955933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10576335852292441197274577 7932251889219330897955933)
                    ·
                      refine ⟨2974594458457249086733475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932251889219330897955933 2974594458457249086733475)
                      ·
                        rfl

theorem cell23_5793002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_5793002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793002 prefixEnd_5793002 := by exact prefixLift 5793002
  have htrace : WordTrace (prefixWord ++ tailWord_5793002) baseStart_5793002 baseEnd_5793002 := by
    simpa [prefixWord, tailWord_5793002, baseEnd_5793002] using wordTrace_append hprefix tailTrace_5793002
  have hstable : (prefixWord ++ tailWord_5793002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793002).length < 2 ^ (prefixWord ++ tailWord_5793002).sum := by decide
  have hdescent : baseEnd_5793002 < baseStart_5793002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793032 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_5793032 : Nat := 118140960795 + 5793032 * 2 ^ 59
def prefixEnd_5793032 : Nat := 4983230072969 + 3 ^ 40 * 5793032 * 2
def baseEnd_5793032 : Nat := 2974609862876883969358337

theorem tailTrace_5793032 : CollatzResearch.WordTrace tailWord_5793032 prefixEnd_5793032 2974609862876883969358337 := by
  unfold tailWord_5793032
  simp only [CollatzResearch.WordTrace]
  refine ⟨105644617574420954971426675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140859490099227939961902233 105644617574420954971426675)
  ·
    refine ⟨158466926361631432457140013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105644617574420954971426675 158466926361631432457140013)
    ·
      refine ⟨59425097385611787171427505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158466926361631432457140013 59425097385611787171427505)
      ·
        refine ⟨44568823039208840378570629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59425097385611787171427505 44568823039208840378570629)
        ·
          refine ⟨8356654319851657570981993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44568823039208840378570629 8356654319851657570981993)
          ·
            refine ⟨6267490739888743178236495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8356654319851657570981993 6267490739888743178236495)
            ·
              refine ⟨9401236109833114767354743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267490739888743178236495 9401236109833114767354743)
              ·
                refine ⟨14101854164749672151032115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9401236109833114767354743 14101854164749672151032115)
                ·
                  refine ⟨21152781247124508226548173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14101854164749672151032115 21152781247124508226548173)
                  ·
                    refine ⟨7932292967671690584955565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21152781247124508226548173 7932292967671690584955565)
                    ·
                      refine ⟨2974609862876883969358337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932292967671690584955565 2974609862876883969358337)
                      ·
                        rfl

theorem cell23_5793032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_5793032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793032 prefixEnd_5793032 := by exact prefixLift 5793032
  have htrace : WordTrace (prefixWord ++ tailWord_5793032) baseStart_5793032 baseEnd_5793032 := by
    simpa [prefixWord, tailWord_5793032, baseEnd_5793032] using wordTrace_append hprefix tailTrace_5793032
  have hstable : (prefixWord ++ tailWord_5793032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793032).length < 2 ^ (prefixWord ++ tailWord_5793032).sum := by decide
  have hdescent : baseEnd_5793032 < baseStart_5793032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793071 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_5793071 : Nat := 118140960795 + 5793071 * 2 ^ 59
def prefixEnd_5793071 : Nat := 4983230072969 + 3 ^ 40 * 5793071 * 2
def baseEnd_5793071 : Nat := 2974629888622409316770657

theorem tailTrace_5793071 : CollatzResearch.WordTrace tailWord_5793071 prefixEnd_5793071 2974629888622409316770657 := by
  unfold tailWord_5793071
  simp only [CollatzResearch.WordTrace]
  refine ⟨211290657595700619603523067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140860438397133746402348711 211290657595700619603523067)
  ·
    refine ⟨316935986393550929405284601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211290657595700619603523067 316935986393550929405284601)
    ·
      refine ⟨237701989795163197053963451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316935986393550929405284601 237701989795163197053963451)
      ·
        refine ⟨356552984692744795580945177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237701989795163197053963451 356552984692744795580945177)
        ·
          refine ⟨267414738519558596685708883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356552984692744795580945177 267414738519558596685708883)
          ·
            refine ⟨401122107779337895028563325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267414738519558596685708883 401122107779337895028563325)
            ·
              refine ⟨150420790417251710635711247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401122107779337895028563325 150420790417251710635711247)
              ·
                refine ⟨225631185625877565953566871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150420790417251710635711247 225631185625877565953566871)
                ·
                  refine ⟨338446778438816348930350307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225631185625877565953566871 338446778438816348930350307)
                  ·
                    refine ⟨507670167658224523395525461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338446778438816348930350307 507670167658224523395525461)
                    ·
                      refine ⟨2974629888622409316770657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 507670167658224523395525461 2974629888622409316770657)
                      ·
                        rfl

theorem cell23_5793071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_5793071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793071 prefixEnd_5793071 := by exact prefixLift 5793071
  have htrace : WordTrace (prefixWord ++ tailWord_5793071) baseStart_5793071 baseEnd_5793071 := by
    simpa [prefixWord, tailWord_5793071, baseEnd_5793071] using wordTrace_append hprefix tailTrace_5793071
  have hstable : (prefixWord ++ tailWord_5793071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793071).length < 2 ^ (prefixWord ++ tailWord_5793071).sum := by decide
  have hdescent : baseEnd_5793071 < baseStart_5793071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793072 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2]
def baseStart_5793072 : Nat := 118140960795 + 5793072 * 2 ^ 59
def prefixEnd_5793072 : Nat := 4983230072969 + 3 ^ 40 * 5793072 * 2
def baseEnd_5793072 : Nat := 2974630402103063812858153

theorem tailTrace_5793072 : CollatzResearch.WordTrace tailWord_5793072 prefixEnd_5793072 2974630402103063812858153 := by
  unfold tailWord_5793072
  simp only [CollatzResearch.WordTrace]
  refine ⟨105645347034348498387154735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140860462712464664516206313 105645347034348498387154735)
  ·
    refine ⟨158468020551522747580732103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105645347034348498387154735 158468020551522747580732103)
    ·
      refine ⟨237702030827284121371098155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158468020551522747580732103 237702030827284121371098155)
      ·
        refine ⟨356553046240926182056647233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237702030827284121371098155 356553046240926182056647233)
        ·
          refine ⟨267414784680694636542485425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356553046240926182056647233 267414784680694636542485425)
          ·
            refine ⟨200561088510520977406864069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267414784680694636542485425 200561088510520977406864069)
            ·
              refine ⟨37605204095722683263787013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200561088510520977406864069 37605204095722683263787013)
              ·
                refine ⟨7050975767948003111960065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37605204095722683263787013 7050975767948003111960065)
                ·
                  refine ⟨5288231825961002333970049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7050975767948003111960065 5288231825961002333970049)
                  ·
                    refine ⟨3966173869470751750477537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5288231825961002333970049 3966173869470751750477537)
                    ·
                      refine ⟨2974630402103063812858153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966173869470751750477537 2974630402103063812858153)
                      ·
                        rfl

theorem cell23_5793072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2].length) (baseStart_5793072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793072 prefixEnd_5793072 := by exact prefixLift 5793072
  have htrace : WordTrace (prefixWord ++ tailWord_5793072) baseStart_5793072 baseEnd_5793072 := by
    simpa [prefixWord, tailWord_5793072, baseEnd_5793072] using wordTrace_append hprefix tailTrace_5793072
  have hstable : (prefixWord ++ tailWord_5793072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793072).length < 2 ^ (prefixWord ++ tailWord_5793072).sum := by decide
  have hdescent : baseEnd_5793072 < baseStart_5793072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793088 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_5793088 : Nat := 118140960795 + 5793088 * 2 ^ 59
def prefixEnd_5793088 : Nat := 4983230072969 + 3 ^ 40 * 5793088 * 2
def baseEnd_5793088 : Nat := 2974638617793535750258079

theorem tailTrace_5793088 : CollatzResearch.WordTrace tailWord_5793088 prefixEnd_5793088 2974638617793535750258079 := by
  unfold tailWord_5793088
  simp only [CollatzResearch.WordTrace]
  refine ⟨105645638818319515753445959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140860851757759354337927945 105645638818319515753445959)
  ·
    refine ⟨158468458227479273630168939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105645638818319515753445959 158468458227479273630168939)
    ·
      refine ⟨237702687341218910445253409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158468458227479273630168939 237702687341218910445253409)
      ·
        refine ⟨178277015505914182833940057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237702687341218910445253409 178277015505914182833940057)
        ·
          refine ⟨133707761629435637125455043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178277015505914182833940057 133707761629435637125455043)
          ·
            refine ⟨200561642444153455688182565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133707761629435637125455043 200561642444153455688182565)
            ·
              refine ⟨37605307958278772941534231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200561642444153455688182565 37605307958278772941534231)
              ·
                refine ⟨56407961937418159412301347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37605307958278772941534231 56407961937418159412301347)
                ·
                  refine ⟨84611942906127239118452021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56407961937418159412301347 84611942906127239118452021)
                  ·
                    refine ⟨7932369647449428667354877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84611942906127239118452021 7932369647449428667354877)
                    ·
                      refine ⟨2974638617793535750258079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932369647449428667354877 2974638617793535750258079)
                      ·
                        rfl

theorem cell23_5793088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_5793088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793088 prefixEnd_5793088 := by exact prefixLift 5793088
  have htrace : WordTrace (prefixWord ++ tailWord_5793088) baseStart_5793088 baseEnd_5793088 := by
    simpa [prefixWord, tailWord_5793088, baseEnd_5793088] using wordTrace_append hprefix tailTrace_5793088
  have hstable : (prefixWord ++ tailWord_5793088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793088).length < 2 ^ (prefixWord ++ tailWord_5793088).sum := by decide
  have hdescent : baseEnd_5793088 < baseStart_5793088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793145 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 6, 2]
def baseStart_5793145 : Nat := 118140960795 + 5793145 * 2 ^ 59
def prefixEnd_5793145 : Nat := 4983230072969 + 3 ^ 40 * 5793145 * 2
def baseEnd_5793145 : Nat := 2974667886190842027245317

theorem tailTrace_5793145 : CollatzResearch.WordTrace tailWord_5793145 prefixEnd_5793145 2974667886190842027245317 := by
  unfold tailWord_5793145
  simp only [CollatzResearch.WordTrace]
  refine ⟨211293356597432530241716889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140862237731621686827811259 211293356597432530241716889)
  ·
    refine ⟨158470017448074397681287667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211293356597432530241716889 158470017448074397681287667)
    ·
      refine ⟨237705026172111596521931501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158470017448074397681287667 237705026172111596521931501)
      ·
        refine ⟨89139384814541848695724313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237705026172111596521931501 89139384814541848695724313)
        ·
          refine ⟨66854538610906386521793235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89139384814541848695724313 66854538610906386521793235)
          ·
            refine ⟨100281807916359579782689853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66854538610906386521793235 100281807916359579782689853)
            ·
              refine ⟨37605677968634842418508695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100281807916359579782689853 37605677968634842418508695)
              ·
                refine ⟨56408516952952263627763043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37605677968634842418508695 56408516952952263627763043)
                ·
                  refine ⟨84612775429428395441644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56408516952952263627763043 84612775429428395441644565)
                  ·
                    refine ⟨3966223848254456036327089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84612775429428395441644565 3966223848254456036327089)
                    ·
                      refine ⟨2974667886190842027245317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966223848254456036327089 2974667886190842027245317)
                      ·
                        rfl

theorem cell23_5793145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_5793145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793145 prefixEnd_5793145 := by exact prefixLift 5793145
  have htrace : WordTrace (prefixWord ++ tailWord_5793145) baseStart_5793145 baseEnd_5793145 := by
    simpa [prefixWord, tailWord_5793145, baseEnd_5793145] using wordTrace_append hprefix tailTrace_5793145
  have hstable : (prefixWord ++ tailWord_5793145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793145).length < 2 ^ (prefixWord ++ tailWord_5793145).sum := by decide
  have hdescent : baseEnd_5793145 < baseStart_5793145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793155 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 5, 4]
def baseStart_5793155 : Nat := 118140960795 + 5793155 * 2 ^ 59
def prefixEnd_5793155 : Nat := 4983230072969 + 3 ^ 40 * 5793155 * 2
def baseEnd_5793155 : Nat := 991557673665795662706757

theorem tailTrace_5793155 : CollatzResearch.WordTrace tailWord_5793155 prefixEnd_5793155 991557673665795662706757 := by
  unfold tailWord_5793155
  simp only [CollatzResearch.WordTrace]
  refine ⟨211293721327396301949580919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140862480884930867966387279 211293721327396301949580919)
  ·
    refine ⟨316940581991094452924371379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211293721327396301949580919 316940581991094452924371379)
    ·
      refine ⟨475410872986641679386557069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316940581991094452924371379 475410872986641679386557069)
      ·
        refine ⟨178279077369990629769958901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475410872986641679386557069 178279077369990629769958901)
        ·
          refine ⟨16713663503436621540933647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178279077369990629769958901 16713663503436621540933647)
          ·
            refine ⟨25070495255154932311400471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16713663503436621540933647 25070495255154932311400471)
            ·
              refine ⟨37605742882732398467100707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25070495255154932311400471 37605742882732398467100707)
              ·
                refine ⟨56408614324098597700651061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37605742882732398467100707 56408614324098597700651061)
                ·
                  refine ⟨5288307592884243534436037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56408614324098597700651061 5288307592884243534436037)
                  ·
                    refine ⟨991557673665795662706757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288307592884243534436037 991557673665795662706757)
                    ·
                      rfl

theorem cell23_5793155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 4].length) (baseStart_5793155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793155 prefixEnd_5793155 := by exact prefixLift 5793155
  have htrace : WordTrace (prefixWord ++ tailWord_5793155) baseStart_5793155 baseEnd_5793155 := by
    simpa [prefixWord, tailWord_5793155, baseEnd_5793155] using wordTrace_append hprefix tailTrace_5793155
  have hstable : (prefixWord ++ tailWord_5793155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793155).length < 2 ^ (prefixWord ++ tailWord_5793155).sum := by decide
  have hdescent : baseEnd_5793155 < baseStart_5793155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793208 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_5793208 : Nat := 118140960795 + 5793208 * 2 ^ 59
def prefixEnd_5793208 : Nat := 4983230072969 + 3 ^ 40 * 5793208 * 2
def baseEnd_5793208 : Nat := 2974700235472075280757527

theorem tailTrace_5793208 : CollatzResearch.WordTrace tailWord_5793208 prefixEnd_5793208 2974700235472075280757527 := by
  unfold tailWord_5793208
  simp only [CollatzResearch.WordTrace]
  refine ⟨105647827198102146000630139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140863769597469528000840185 105647827198102146000630139)
  ·
    refine ⟨158471740797153219000945209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105647827198102146000630139 158471740797153219000945209)
    ·
      refine ⟨118853805597864914250708907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158471740797153219000945209 118853805597864914250708907)
      ·
        refine ⟨178280708396797371376063361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118853805597864914250708907 178280708396797371376063361)
        ·
          refine ⟨133710531297598028532047521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178280708396797371376063361 133710531297598028532047521)
          ·
            refine ⟨100282898473198521399035641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133710531297598028532047521 100282898473198521399035641)
            ·
              refine ⟨75212173854898891049276731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100282898473198521399035641 75212173854898891049276731)
              ·
                refine ⟨112818260782348336573915097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75212173854898891049276731 112818260782348336573915097)
                ·
                  refine ⟨84613695586761252430436323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112818260782348336573915097 84613695586761252430436323)
                  ·
                    refine ⟨126920543380141878645654485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84613695586761252430436323 126920543380141878645654485)
                    ·
                      refine ⟨2974700235472075280757527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126920543380141878645654485 2974700235472075280757527)
                      ·
                        rfl

theorem cell23_5793208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_5793208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793208 prefixEnd_5793208 := by exact prefixLift 5793208
  have htrace : WordTrace (prefixWord ++ tailWord_5793208) baseStart_5793208 baseEnd_5793208 := by
    simpa [prefixWord, tailWord_5793208, baseEnd_5793208] using wordTrace_append hprefix tailTrace_5793208
  have hstable : (prefixWord ++ tailWord_5793208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793208).length < 2 ^ (prefixWord ++ tailWord_5793208).sum := by decide
  have hdescent : baseEnd_5793208 < baseStart_5793208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793265 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_5793265 : Nat := 118140960795 + 5793265 * 2 ^ 59
def prefixEnd_5793265 : Nat := 4983230072969 + 3 ^ 40 * 5793265 * 2
def baseEnd_5793265 : Nat := 2974729503869381557744765

theorem tailTrace_5793265 : CollatzResearch.WordTrace tailWord_5793265 prefixEnd_5793265 2974729503869381557744765 := by
  unfold tailWord_5793265
  simp only [CollatzResearch.WordTrace]
  refine ⟨211297733356997790736085249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140865155571331860490723499 211297733356997790736085249)
  ·
    refine ⟨158473300017748343052063937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211297733356997790736085249 158473300017748343052063937)
    ·
      refine ⟨118854975013311257289047953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158473300017748343052063937 118854975013311257289047953)
      ·
        refine ⟨89141231259983442966785965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118854975013311257289047953 89141231259983442966785965)
        ·
          refine ⟨33427961722493791112544737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89141231259983442966785965 33427961722493791112544737)
          ·
            refine ⟨25070971291870343334408553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33427961722493791112544737 25070971291870343334408553)
            ·
              refine ⟨18803228468902757500806415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25070971291870343334408553 18803228468902757500806415)
              ·
                refine ⟨28204842703354136251209623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18803228468902757500806415 28204842703354136251209623)
                ·
                  refine ⟨42307264055031204376814435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28204842703354136251209623 42307264055031204376814435)
                  ·
                    refine ⟨63460896082546806565221653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42307264055031204376814435 63460896082546806565221653)
                    ·
                      refine ⟨2974729503869381557744765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63460896082546806565221653 2974729503869381557744765)
                      ·
                        rfl

theorem cell23_5793265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_5793265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793265 prefixEnd_5793265 := by exact prefixLift 5793265
  have htrace : WordTrace (prefixWord ++ tailWord_5793265) baseStart_5793265 baseEnd_5793265 := by
    simpa [prefixWord, tailWord_5793265, baseEnd_5793265] using wordTrace_append hprefix tailTrace_5793265
  have hstable : (prefixWord ++ tailWord_5793265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793265).length < 2 ^ (prefixWord ++ tailWord_5793265).sum := by decide
  have hdescent : baseEnd_5793265 < baseStart_5793265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793269 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5793269 : Nat := 118140960795 + 5793269 * 2 ^ 59
def prefixEnd_5793269 : Nat := 4983230072969 + 3 ^ 40 * 5793269 * 2
def baseEnd_5793269 : Nat := 2974731557791999542094747

theorem tailTrace_5793269 : CollatzResearch.WordTrace tailWord_5793269 prefixEnd_5793269 2974731557791999542094747 := by
  unfold tailWord_5793269
  simp only [CollatzResearch.WordTrace]
  refine ⟨211297879248983299419230861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140865252832655532946153907 211297879248983299419230861)
  ·
    refine ⟨79236704718368737282211573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211297879248983299419230861 79236704718368737282211573)
    ·
      refine ⟨7428441067347069120207335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79236704718368737282211573 7428441067347069120207335)
      ·
        refine ⟨11142661601020603680311003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428441067347069120207335 11142661601020603680311003)
        ·
          refine ⟨16713992401530905520466505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11142661601020603680311003 16713992401530905520466505)
          ·
            refine ⟨12535494301148179140349879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16713992401530905520466505 12535494301148179140349879)
            ·
              refine ⟨18803241451722268710524819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535494301148179140349879 18803241451722268710524819)
              ·
                refine ⟨28204862177583403065787229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18803241451722268710524819 28204862177583403065787229)
                ·
                  refine ⟨10576823316593776149670211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28204862177583403065787229 10576823316593776149670211)
                  ·
                    refine ⟨15865234974890664224505317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10576823316593776149670211 15865234974890664224505317)
                    ·
                      refine ⟨2974731557791999542094747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15865234974890664224505317 2974731557791999542094747)
                      ·
                        rfl

theorem cell23_5793269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5793269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793269 prefixEnd_5793269 := by exact prefixLift 5793269
  have htrace : WordTrace (prefixWord ++ tailWord_5793269) baseStart_5793269 baseEnd_5793269 := by
    simpa [prefixWord, tailWord_5793269, baseEnd_5793269] using wordTrace_append hprefix tailTrace_5793269
  have hstable : (prefixWord ++ tailWord_5793269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793269).length < 2 ^ (prefixWord ++ tailWord_5793269).sum := by decide
  have hdescent : baseEnd_5793269 < baseStart_5793269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793272 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_5793272 : Nat := 118140960795 + 5793272 * 2 ^ 59
def prefixEnd_5793272 : Nat := 4983230072969 + 3 ^ 40 * 5793272 * 2
def baseEnd_5793272 : Nat := 2974733098233963030357233

theorem tailTrace_5793272 : CollatzResearch.WordTrace tailWord_5793272 prefixEnd_5793272 2974733098233963030357233 := by
  unfold tailWord_5793272
  simp only [CollatzResearch.WordTrace]
  refine ⟨105648994333986215465795035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140865325778648287287726713 105648994333986215465795035)
  ·
    refine ⟨158473491500979323198692553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105648994333986215465795035 158473491500979323198692553)
    ·
      refine ⟨118855118625734492399019415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158473491500979323198692553 118855118625734492399019415)
      ·
        refine ⟨178282677938601738598529123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118855118625734492399019415 178282677938601738598529123)
        ·
          refine ⟨267424016907902607897793685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178282677938601738598529123 267424016907902607897793685)
          ·
            refine ⟨12535500792557934745209079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 267424016907902607897793685 12535500792557934745209079)
            ·
              refine ⟨18803251188836902117813619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535500792557934745209079 18803251188836902117813619)
              ·
                refine ⟨28204876783255353176720429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18803251188836902117813619 28204876783255353176720429)
                ·
                  refine ⟨10576828793720757441270161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28204876783255353176720429 10576828793720757441270161)
                  ·
                    refine ⟨7932621595290568080952621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10576828793720757441270161 7932621595290568080952621)
                    ·
                      refine ⟨2974733098233963030357233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932621595290568080952621 2974733098233963030357233)
                      ·
                        rfl

theorem cell23_5793272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_5793272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793272 prefixEnd_5793272 := by exact prefixLift 5793272
  have htrace : WordTrace (prefixWord ++ tailWord_5793272) baseStart_5793272 baseEnd_5793272 := by
    simpa [prefixWord, tailWord_5793272, baseEnd_5793272] using wordTrace_append hprefix tailTrace_5793272
  have hstable : (prefixWord ++ tailWord_5793272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793272).length < 2 ^ (prefixWord ++ tailWord_5793272).sum := by decide
  have hdescent : baseEnd_5793272 < baseStart_5793272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793289 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 1, 2, 3]
def baseStart_5793289 : Nat := 118140960795 + 5793289 * 2 ^ 59
def prefixEnd_5793289 : Nat := 4983230072969 + 3 ^ 40 * 5793289 * 2
def baseEnd_5793289 : Nat := 2974741827405089463844655

theorem tailTrace_5793289 : CollatzResearch.WordTrace tailWord_5793289 prefixEnd_5793289 2974741827405089463844655 := by
  unfold tailWord_5793289
  simp only [CollatzResearch.WordTrace]
  refine ⟨211298608708910842834958921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140865739139273895223305947 211298608708910842834958921)
  ·
    refine ⟨158473956531683132126219191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211298608708910842834958921 158473956531683132126219191)
    ·
      refine ⟨237710934797524698189328787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158473956531683132126219191 237710934797524698189328787)
      ·
        refine ⟨356566402196287047283993181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237710934797524698189328787 356566402196287047283993181)
        ·
          refine ⟨133712400823607642731497443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356566402196287047283993181 133712400823607642731497443)
          ·
            refine ⟨200568601235411464097246165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133712400823607642731497443 200568601235411464097246165)
            ·
              refine ⟨4700826591454956189779207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200568601235411464097246165 4700826591454956189779207)
              ·
                refine ⟨7051239887182434284668811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700826591454956189779207 7051239887182434284668811)
                ·
                  refine ⟨10576859830773651427003217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7051239887182434284668811 10576859830773651427003217)
                  ·
                    refine ⟨7932644873080238570252413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10576859830773651427003217 7932644873080238570252413)
                    ·
                      refine ⟨2974741827405089463844655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932644873080238570252413 2974741827405089463844655)
                      ·
                        rfl

theorem cell23_5793289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 2, 3].length) (baseStart_5793289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793289 prefixEnd_5793289 := by exact prefixLift 5793289
  have htrace : WordTrace (prefixWord ++ tailWord_5793289) baseStart_5793289 baseEnd_5793289 := by
    simpa [prefixWord, tailWord_5793289, baseEnd_5793289] using wordTrace_append hprefix tailTrace_5793289
  have hstable : (prefixWord ++ tailWord_5793289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793289).length < 2 ^ (prefixWord ++ tailWord_5793289).sum := by decide
  have hdescent : baseEnd_5793289 < baseStart_5793289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793329 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_5793329 : Nat := 118140960795 + 5793329 * 2 ^ 59
def prefixEnd_5793329 : Nat := 4983230072969 + 3 ^ 40 * 5793329 * 2
def baseEnd_5793329 : Nat := 2974762366631269307344471

theorem tailTrace_5793329 : CollatzResearch.WordTrace tailWord_5793329 prefixEnd_5793329 2974762366631269307344471 := by
  unfold tailWord_5793329
  simp only [CollatzResearch.WordTrace]
  refine ⟨211300067628765929666415041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140866711752510619777610027 211300067628765929666415041)
  ·
    refine ⟨158475050721574447249811281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211300067628765929666415041 158475050721574447249811281)
    ·
      refine ⟨118856288041180835437358461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158475050721574447249811281 118856288041180835437358461)
      ·
        refine ⟨44571108015442813289009423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118856288041180835437358461 44571108015442813289009423)
        ·
          refine ⟨66856662023164219933514135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44571108015442813289009423 66856662023164219933514135)
          ·
            refine ⟨100284993034746329900271203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66856662023164219933514135 100284993034746329900271203)
            ·
              refine ⟨150427489552119494850406805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100284993034746329900271203 150427489552119494850406805)
              ·
                refine ⟨7051288572755601321112819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150427489552119494850406805 7051288572755601321112819)
                ·
                  refine ⟨10576932859133401981669229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7051288572755601321112819 10576932859133401981669229)
                  ·
                    refine ⟨3966349822175025743125961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10576932859133401981669229 3966349822175025743125961)
                    ·
                      refine ⟨2974762366631269307344471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966349822175025743125961 2974762366631269307344471)
                      ·
                        rfl

theorem cell23_5793329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_5793329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793329 prefixEnd_5793329 := by exact prefixLift 5793329
  have htrace : WordTrace (prefixWord ++ tailWord_5793329) baseStart_5793329 baseEnd_5793329 := by
    simpa [prefixWord, tailWord_5793329, baseEnd_5793329] using wordTrace_append hprefix tailTrace_5793329
  have hstable : (prefixWord ++ tailWord_5793329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793329).length < 2 ^ (prefixWord ++ tailWord_5793329).sum := by decide
  have hdescent : baseEnd_5793329 < baseStart_5793329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793416 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 7]
def baseStart_5793416 : Nat := 118140960795 + 5793416 * 2 ^ 59
def prefixEnd_5793416 : Nat := 4983230072969 + 3 ^ 40 * 5793416 * 2
def baseEnd_5793416 : Nat := 330534115494245607439619

theorem tailTrace_5793416 : CollatzResearch.WordTrace tailWord_5793416 prefixEnd_5793416 330534115494245607439619 := by
  unfold tailWord_5793416
  simp only [CollatzResearch.WordTrace]
  refine ⟨105651620389725371762416051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140868827186300495683221401 105651620389725371762416051)
  ·
    refine ⟨158477430584588057643624077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105651620389725371762416051 158477430584588057643624077)
    ·
      refine ⟨59429036469220521616359029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158477430584588057643624077 59429036469220521616359029)
      ·
        refine ⟨5571472168989423901533659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59429036469220521616359029 5571472168989423901533659)
        ·
          refine ⟨8357208253484135852300489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571472168989423901533659 8357208253484135852300489)
          ·
            refine ⟨6267906190113101889225367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8357208253484135852300489 6267906190113101889225367)
            ·
              refine ⟨9401859285169652833838051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267906190113101889225367 9401859285169652833838051)
              ·
                refine ⟨14102788927754479250757077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9401859285169652833838051 14102788927754479250757077)
                ·
                  refine ⟨330534115494245607439619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14102788927754479250757077 330534115494245607439619)
                  ·
                    rfl

theorem cell23_5793416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_5793416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793416 prefixEnd_5793416 := by exact prefixLift 5793416
  have htrace : WordTrace (prefixWord ++ tailWord_5793416) baseStart_5793416 baseEnd_5793416 := by
    simpa [prefixWord, tailWord_5793416, baseEnd_5793416] using wordTrace_append hprefix tailTrace_5793416
  have hstable : (prefixWord ++ tailWord_5793416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793416).length < 2 ^ (prefixWord ++ tailWord_5793416).sum := by decide
  have hdescent : baseEnd_5793416 < baseStart_5793416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793422 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5793422 : Nat := 118140960795 + 5793422 * 2 ^ 59
def prefixEnd_5793422 : Nat := 4983230072969 + 3 ^ 40 * 5793422 * 2
def baseEnd_5793422 : Nat := 2974810120332137443481543

theorem tailTrace_5793422 : CollatzResearch.WordTrace tailWord_5793422 prefixEnd_5793422 2974810120332137443481543 := by
  unfold tailWord_5793422
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412932452178625818693815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140868973078286004366367013 26412932452178625818693815)
  ·
    refine ⟨39619398678267938728040723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412932452178625818693815 39619398678267938728040723)
    ·
      refine ⟨59429098017401908092061085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39619398678267938728040723 59429098017401908092061085)
      ·
        refine ⟨22285911756525715534522907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59429098017401908092061085 22285911756525715534522907)
        ·
          refine ⟨33428867634788573301784361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22285911756525715534522907 33428867634788573301784361)
          ·
            refine ⟨25071650726091429976338271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33428867634788573301784361 25071650726091429976338271)
            ·
              refine ⟨37607476089137144964507407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25071650726091429976338271 37607476089137144964507407)
              ·
                refine ⟨56411214133705717446761111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37607476089137144964507407 56411214133705717446761111)
                ·
                  refine ⟨84616821200558576170141667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56411214133705717446761111 84616821200558576170141667)
                  ·
                    refine ⟨126925231800837864255212501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84616821200558576170141667 126925231800837864255212501)
                    ·
                      refine ⟨2974810120332137443481543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126925231800837864255212501 2974810120332137443481543)
                      ·
                        rfl

theorem cell23_5793422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5793422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793422 prefixEnd_5793422 := by exact prefixLift 5793422
  have htrace : WordTrace (prefixWord ++ tailWord_5793422) baseStart_5793422 baseEnd_5793422 := by
    simpa [prefixWord, tailWord_5793422, baseEnd_5793422] using wordTrace_append hprefix tailTrace_5793422
  have hstable : (prefixWord ++ tailWord_5793422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793422).length < 2 ^ (prefixWord ++ tailWord_5793422).sum := by decide
  have hdescent : baseEnd_5793422 < baseStart_5793422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793425 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_5793425 : Nat := 118140960795 + 5793425 * 2 ^ 59
def prefixEnd_5793425 : Nat := 4983230072969 + 3 ^ 40 * 5793425 * 2
def baseEnd_5793425 : Nat := 991603886924700310581343

theorem tailTrace_5793425 : CollatzResearch.WordTrace tailWord_5793425 prefixEnd_5793425 991603886924700310581343 := by
  unfold tailWord_5793425
  simp only [CollatzResearch.WordTrace]
  refine ⟨211303569036418138061909729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140869046024278758707939819 211303569036418138061909729)
  ·
    refine ⟨158477676777313603546432297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211303569036418138061909729 158477676777313603546432297)
    ·
      refine ⟨118858257582985202659824223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158477676777313603546432297 118858257582985202659824223)
      ·
        refine ⟨178287386374477803989736335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118858257582985202659824223 178287386374477803989736335)
        ·
          refine ⟨267431079561716705984604503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178287386374477803989736335 267431079561716705984604503)
          ·
            refine ⟨401146619342575058976906755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267431079561716705984604503 401146619342575058976906755)
            ·
              refine ⟨601719929013862588465360133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401146619342575058976906755 601719929013862588465360133)
              ·
                refine ⟨112822486690099235337255025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601719929013862588465360133 112822486690099235337255025)
                ·
                  refine ⟨84616865017574426502941269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112822486690099235337255025 84616865017574426502941269)
                  ·
                    refine ⟨991603886924700310581343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84616865017574426502941269 991603886924700310581343)
                    ·
                      rfl

theorem cell23_5793425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_5793425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793425 prefixEnd_5793425 := by exact prefixLift 5793425
  have htrace : WordTrace (prefixWord ++ tailWord_5793425) baseStart_5793425 baseEnd_5793425 := by
    simpa [prefixWord, tailWord_5793425, baseEnd_5793425] using wordTrace_append hprefix tailTrace_5793425
  have hstable : (prefixWord ++ tailWord_5793425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793425).length < 2 ^ (prefixWord ++ tailWord_5793425).sum := by decide
  have hdescent : baseEnd_5793425 < baseStart_5793425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793469 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5793469 : Nat := 118140960795 + 5793469 * 2 ^ 59
def prefixEnd_5793469 : Nat := 4983230072969 + 3 ^ 40 * 5793469 * 2
def baseEnd_5793469 : Nat := 2974834253922898759593827

theorem tailTrace_5793469 : CollatzResearch.WordTrace tailWord_5793469 prefixEnd_5793469 2974834253922898759593827 := by
  unfold tailWord_5793469
  simp only [CollatzResearch.WordTrace]
  refine ⟨211305173848258733576511461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140870115898839155717674307 211305173848258733576511461)
  ·
    refine ⟨39619720096548512545595899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211305173848258733576511461 39619720096548512545595899)
    ·
      refine ⟨59429580144822768818393849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39619720096548512545595899 59429580144822768818393849)
      ·
        refine ⟨44572185108617076613795387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59429580144822768818393849 44572185108617076613795387)
        ·
          refine ⟨66858277662925614920693081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44572185108617076613795387 66858277662925614920693081)
          ·
            refine ⟨50143708247194211190519811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66858277662925614920693081 50143708247194211190519811)
            ·
              refine ⟨75215562370791316785779717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50143708247194211190519811 75215562370791316785779717)
              ·
                refine ⟨14102917944523371897333697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75215562370791316785779717 14102917944523371897333697)
                ·
                  refine ⟨10577188458392528923000273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14102917944523371897333697 10577188458392528923000273)
                  ·
                    refine ⟨7932891343794396692250205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10577188458392528923000273 7932891343794396692250205)
                    ·
                      refine ⟨2974834253922898759593827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7932891343794396692250205 2974834253922898759593827)
                      ·
                        rfl

theorem cell23_5793469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5793469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793469 prefixEnd_5793469 := by exact prefixLift 5793469
  have htrace : WordTrace (prefixWord ++ tailWord_5793469) baseStart_5793469 baseEnd_5793469 := by
    simpa [prefixWord, tailWord_5793469, baseEnd_5793469] using wordTrace_append hprefix tailTrace_5793469
  have hstable : (prefixWord ++ tailWord_5793469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793469).length < 2 ^ (prefixWord ++ tailWord_5793469).sum := by decide
  have hdescent : baseEnd_5793469 < baseStart_5793469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793500 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5793500 : Nat := 118140960795 + 5793500 * 2 ^ 59
def prefixEnd_5793500 : Nat := 4983230072969 + 3 ^ 40 * 5793500 * 2
def baseEnd_5793500 : Nat := 2974850171823188138306185

theorem tailTrace_5793500 : CollatzResearch.WordTrace tailWord_5793500 prefixEnd_5793500 2974850171823188138306185 := by
  unfold tailWord_5793500
  simp only [CollatzResearch.WordTrace]
  refine ⟨105653152255573212935444977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140870869674097617247259969 105653152255573212935444977)
  ·
    refine ⟨79239864191679909701583733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105653152255573212935444977 79239864191679909701583733)
    ·
      refine ⟨7428737267969991534523475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79239864191679909701583733 7428737267969991534523475)
      ·
        refine ⟨11143105901954987301785213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428737267969991534523475 11143105901954987301785213)
        ·
          refine ⟨4178664713233120238169455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143105901954987301785213 4178664713233120238169455)
          ·
            refine ⟨6267997069849680357254183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178664713233120238169455 6267997069849680357254183)
            ·
              refine ⟨9401995604774520535881275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6267997069849680357254183 9401995604774520535881275)
              ·
                refine ⟨14102993407161780803821913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9401995604774520535881275 14102993407161780803821913)
                ·
                  refine ⟨10577245055371335602866435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14102993407161780803821913 10577245055371335602866435)
                  ·
                    refine ⟨15865867583057003404299653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10577245055371335602866435 15865867583057003404299653)
                    ·
                      refine ⟨2974850171823188138306185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15865867583057003404299653 2974850171823188138306185)
                      ·
                        rfl

theorem cell23_5793500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5793500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793500 prefixEnd_5793500 := by exact prefixLift 5793500
  have htrace : WordTrace (prefixWord ++ tailWord_5793500) baseStart_5793500 baseEnd_5793500 := by
    simpa [prefixWord, tailWord_5793500, baseEnd_5793500] using wordTrace_append hprefix tailTrace_5793500
  have hstable : (prefixWord ++ tailWord_5793500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793500).length < 2 ^ (prefixWord ++ tailWord_5793500).sum := by decide
  have hdescent : baseEnd_5793500 < baseStart_5793500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793519 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 1, 5]
def baseStart_5793519 : Nat := 118140960795 + 5793519 * 2 ^ 59
def prefixEnd_5793519 : Nat := 4983230072969 + 3 ^ 40 * 5793519 * 2
def baseEnd_5793519 : Nat := 991619975985207854656199

theorem tailTrace_5793519 : CollatzResearch.WordTrace tailWord_5793519 prefixEnd_5793519 991619975985207854656199 := by
  unfold tailWord_5793519
  simp only [CollatzResearch.WordTrace]
  refine ⟨211306997498077592115831611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140871331665385061410554407 211306997498077592115831611)
  ·
    refine ⟨316960496247116388173747417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211306997498077592115831611 316960496247116388173747417)
    ·
      refine ⟨237720372185337291130310563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316960496247116388173747417 237720372185337291130310563)
      ·
        refine ⟨356580558278005936695465845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237720372185337291130310563 356580558278005936695465845)
        ·
          refine ⟨33429427338563056565199923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 356580558278005936695465845 33429427338563056565199923)
          ·
            refine ⟨50144141007844584847799885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33429427338563056565199923 50144141007844584847799885)
            ·
              refine ⟨18804052877941719317924957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50144141007844584847799885 18804052877941719317924957)
              ·
                refine ⟨7051519829228144744221859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18804052877941719317924957 7051519829228144744221859)
                ·
                  refine ⟨10577279743842217116332789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7051519829228144744221859 10577279743842217116332789)
                  ·
                    refine ⟨991619975985207854656199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10577279743842217116332789 991619975985207854656199)
                    ·
                      rfl

theorem cell23_5793519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_5793519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793519 prefixEnd_5793519 := by exact prefixLift 5793519
  have htrace : WordTrace (prefixWord ++ tailWord_5793519) baseStart_5793519 baseEnd_5793519 := by
    simpa [prefixWord, tailWord_5793519, baseEnd_5793519] using wordTrace_append hprefix tailTrace_5793519
  have hstable : (prefixWord ++ tailWord_5793519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793519).length < 2 ^ (prefixWord ++ tailWord_5793519).sum := by decide
  have hdescent : baseEnd_5793519 < baseStart_5793519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793576 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5793576 : Nat := 118140960795 + 5793576 * 2 ^ 59
def prefixEnd_5793576 : Nat := 4983230072969 + 3 ^ 40 * 5793576 * 2
def baseEnd_5793576 : Nat := 2974889196352929840955835

theorem tailTrace_5793576 : CollatzResearch.WordTrace tailWord_5793576 prefixEnd_5793576 2974889196352929840955835 := by
  unfold tailWord_5793576
  simp only [CollatzResearch.WordTrace]
  refine ⟨105654538229435545425328291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140872717639247393900437721 105654538229435545425328291)
  ·
    refine ⟨158481807344153318137992437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105654538229435545425328291 158481807344153318137992437)
    ·
      refine ⟨14857669438514373575436791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158481807344153318137992437 14857669438514373575436791)
      ·
        refine ⟨22286504157771560363155187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14857669438514373575436791 22286504157771560363155187)
        ·
          refine ⟨33429756236657340544732781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22286504157771560363155187 33429756236657340544732781)
          ·
            refine ⟨12536158588746502704274793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33429756236657340544732781 12536158588746502704274793)
            ·
              refine ⟨9402118941559877028206095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12536158588746502704274793 9402118941559877028206095)
              ·
                refine ⟨14103178412339815542309143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402118941559877028206095 14103178412339815542309143)
                ·
                  refine ⟨21154767618509723313463715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14103178412339815542309143 21154767618509723313463715)
                  ·
                    refine ⟨31732151427764584970195573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21154767618509723313463715 31732151427764584970195573)
                    ·
                      refine ⟨2974889196352929840955835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31732151427764584970195573 2974889196352929840955835)
                      ·
                        rfl

theorem cell23_5793576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5793576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793576 prefixEnd_5793576 := by exact prefixLift 5793576
  have htrace : WordTrace (prefixWord ++ tailWord_5793576) baseStart_5793576 baseEnd_5793576 := by
    simpa [prefixWord, tailWord_5793576, baseEnd_5793576] using wordTrace_append hprefix tailTrace_5793576
  have hstable : (prefixWord ++ tailWord_5793576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793576).length < 2 ^ (prefixWord ++ tailWord_5793576).sum := by decide
  have hdescent : baseEnd_5793576 < baseStart_5793576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793639 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 2, 6]
def baseStart_5793639 : Nat := 118140960795 + 5793639 * 2 ^ 59
def prefixEnd_5793639 : Nat := 4983230072969 + 3 ^ 40 * 5793639 * 2
def baseEnd_5793639 : Nat := 991640515211387698156015

theorem tailTrace_5793639 : CollatzResearch.WordTrace tailWord_5793639 prefixEnd_5793639 991640515211387698156015 := by
  unfold tailWord_5793639
  simp only [CollatzResearch.WordTrace]
  refine ⟨211311374257642852610199971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140874249505095235073466647 211311374257642852610199971)
  ·
    refine ⟨316967061386464278915299957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211311374257642852610199971 316967061386464278915299957)
    ·
      refine ⟨29715662004981026148309371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316967061386464278915299957 29715662004981026148309371)
      ·
        refine ⟨44573493007471539222464057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29715662004981026148309371 44573493007471539222464057)
        ·
          refine ⟨33430119755603654416848043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44573493007471539222464057 33430119755603654416848043)
          ·
            refine ⟨50145179633405481625272065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33430119755603654416848043 50145179633405481625272065)
            ·
              refine ⟨37608884725054111218954049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50145179633405481625272065 37608884725054111218954049)
              ·
                refine ⟨28206663543790583414215537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37608884725054111218954049 28206663543790583414215537)
                ·
                  refine ⟨21154997657842937560661653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28206663543790583414215537 21154997657842937560661653)
                  ·
                    refine ⟨991640515211387698156015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21154997657842937560661653 991640515211387698156015)
                    ·
                      rfl

theorem cell23_5793639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_5793639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793639 prefixEnd_5793639 := by exact prefixLift 5793639
  have htrace : WordTrace (prefixWord ++ tailWord_5793639) baseStart_5793639 baseEnd_5793639 := by
    simpa [prefixWord, tailWord_5793639, baseEnd_5793639] using wordTrace_append hprefix tailTrace_5793639
  have hstable : (prefixWord ++ tailWord_5793639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793639).length < 2 ^ (prefixWord ++ tailWord_5793639).sum := by decide
  have hdescent : baseEnd_5793639 < baseStart_5793639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793646 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5793646 : Nat := 118140960795 + 5793646 * 2 ^ 59
def prefixEnd_5793646 : Nat := 4983230072969 + 3 ^ 40 * 5793646 * 2
def baseEnd_5793646 : Nat := 2974925139998744567080513

theorem tailTrace_5793646 : CollatzResearch.WordTrace tailWord_5793646 prefixEnd_5793646 2974925139998744567080513 := by
  unfold tailWord_5793646
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413953696077186600713099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140874419712411661870469861 26413953696077186600713099)
  ·
    refine ⟨39620930544115779901069649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26413953696077186600713099 39620930544115779901069649)
    ·
      refine ⟨29715697908086834925802237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39620930544115779901069649 29715697908086834925802237)
      ·
        refine ⟨11143386715532563097175839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29715697908086834925802237 11143386715532563097175839)
        ·
          refine ⟨16715080073298844645763759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143386715532563097175839 16715080073298844645763759)
          ·
            refine ⟨25072620109948266968645639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16715080073298844645763759 25072620109948266968645639)
            ·
              refine ⟨37608930164922400452968459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25072620109948266968645639 37608930164922400452968459)
              ·
                refine ⟨56413395247383600679452689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37608930164922400452968459 56413395247383600679452689)
                ·
                  refine ⟨42310046435537700509589517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56413395247383600679452689 42310046435537700509589517)
                  ·
                    refine ⟨15866267413326637691096069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42310046435537700509589517 15866267413326637691096069)
                    ·
                      refine ⟨2974925139998744567080513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15866267413326637691096069 2974925139998744567080513)
                      ·
                        rfl

theorem cell23_5793646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5793646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793646 prefixEnd_5793646 := by exact prefixLift 5793646
  have htrace : WordTrace (prefixWord ++ tailWord_5793646) baseStart_5793646 baseEnd_5793646 := by
    simpa [prefixWord, tailWord_5793646, baseEnd_5793646] using wordTrace_append hprefix tailTrace_5793646
  have hstable : (prefixWord ++ tailWord_5793646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793646).length < 2 ^ (prefixWord ++ tailWord_5793646).sum := by decide
  have hdescent : baseEnd_5793646 < baseStart_5793646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793649 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_5793649 : Nat := 118140960795 + 5793649 * 2 ^ 59
def prefixEnd_5793649 : Nat := 4983230072969 + 3 ^ 40 * 5793649 * 2
def baseEnd_5793649 : Nat := 2974926680440708055342999

theorem tailTrace_5793649 : CollatzResearch.WordTrace tailWord_5793649 prefixEnd_5793649 2974926680440708055342999 := by
  unfold tailWord_5793649
  simp only [CollatzResearch.WordTrace]
  refine ⟨211311738987606624318064001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140874492658404416212042667 211311738987606624318064001)
  ·
    refine ⟨158483804240704968238548001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211311738987606624318064001 158483804240704968238548001)
    ·
      refine ⟨118862853180528726178911001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158483804240704968238548001 118862853180528726178911001)
      ·
        refine ⟨89147139885396544634183251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118862853180528726178911001 89147139885396544634183251)
        ·
          refine ⟨133720709828094816951274877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89147139885396544634183251 133720709828094816951274877)
          ·
            refine ⟨50145266185535556356728079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133720709828094816951274877 50145266185535556356728079)
            ·
              refine ⟨75217899278303334535092119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50145266185535556356728079 75217899278303334535092119)
              ·
                refine ⟨112826848917455001802638179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75217899278303334535092119 112826848917455001802638179)
                ·
                  refine ⟨169240273376182502703957269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112826848917455001802638179 169240273376182502703957269)
                  ·
                    refine ⟨7933137814508554814247997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169240273376182502703957269 7933137814508554814247997)
                    ·
                      refine ⟨2974926680440708055342999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7933137814508554814247997 2974926680440708055342999)
                      ·
                        rfl

theorem cell23_5793649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_5793649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793649 prefixEnd_5793649 := by exact prefixLift 5793649
  have htrace : WordTrace (prefixWord ++ tailWord_5793649) baseStart_5793649 baseEnd_5793649 := by
    simpa [prefixWord, tailWord_5793649, baseEnd_5793649] using wordTrace_append hprefix tailTrace_5793649
  have hstable : (prefixWord ++ tailWord_5793649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793649).length < 2 ^ (prefixWord ++ tailWord_5793649).sum := by decide
  have hdescent : baseEnd_5793649 < baseStart_5793649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793669 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 7]
def baseStart_5793669 : Nat := 118140960795 + 5793669 * 2 ^ 59
def prefixEnd_5793669 : Nat := 4983230072969 + 3 ^ 40 * 5793669 * 2
def baseEnd_5793669 : Nat := 330548550005977553010323

theorem tailTrace_5793669 : CollatzResearch.WordTrace tailWord_5793669 prefixEnd_5793669 330548550005977553010323 := by
  unfold tailWord_5793669
  simp only [CollatzResearch.WordTrace]
  refine ⟨211312468447534167733792061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140874978965022778489194707 211312468447534167733792061)
  ·
    refine ⟨79242175667825312900172023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211312468447534167733792061 79242175667825312900172023)
    ·
      refine ⟨118863263501737969350258035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79242175667825312900172023 118863263501737969350258035)
      ·
        refine ⟨178294895252606954025387053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118863263501737969350258035 178294895252606954025387053)
        ·
          refine ⟨66860585719727607759520145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178294895252606954025387053 66860585719727607759520145)
          ·
            refine ⟨50145439289795705819640109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66860585719727607759520145 50145439289795705819640109)
            ·
              refine ⟨18804539733673389682365041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50145439289795705819640109 18804539733673389682365041)
              ·
                refine ⟨14103404800255042261773781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18804539733673389682365041 14103404800255042261773781)
                ·
                  refine ⟨330548550005977553010323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14103404800255042261773781 330548550005977553010323)
                  ·
                    rfl

theorem cell23_5793669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_5793669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793669 prefixEnd_5793669 := by exact prefixLift 5793669
  have htrace : WordTrace (prefixWord ++ tailWord_5793669) baseStart_5793669 baseEnd_5793669 := by
    simpa [prefixWord, tailWord_5793669, baseEnd_5793669] using wordTrace_append hprefix tailTrace_5793669
  have hstable : (prefixWord ++ tailWord_5793669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793669).length < 2 ^ (prefixWord ++ tailWord_5793669).sum := by decide
  have hdescent : baseEnd_5793669 < baseStart_5793669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793699 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 4, 5]
def baseStart_5793699 : Nat := 118140960795 + 5793699 * 2 ^ 59
def prefixEnd_5793699 : Nat := 4983230072969 + 3 ^ 40 * 5793699 * 2
def baseEnd_5793699 : Nat := 991650784824477619905923

theorem tailTrace_5793699 : CollatzResearch.WordTrace tailWord_5793699 prefixEnd_5793699 991650784824477619905923 := by
  unfold tailWord_5793699
  simp only [CollatzResearch.WordTrace]
  refine ⟨211313562637425482857384151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140875708424950321904922767 211313562637425482857384151)
  ·
    refine ⟨316970343956138224286076227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211313562637425482857384151 316970343956138224286076227)
    ·
      refine ⟨475455515934207336429114341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316970343956138224286076227 475455515934207336429114341)
      ·
        refine ⟨89147909237663875580458939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 475455515934207336429114341 89147909237663875580458939)
        ·
          refine ⟨133721863856495813370688409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89147909237663875580458939 133721863856495813370688409)
          ·
            refine ⟨100291397892371860028016307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133721863856495813370688409 100291397892371860028016307)
            ·
              refine ⟨150437096838557790042024461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100291397892371860028016307 150437096838557790042024461)
              ·
                refine ⟨56413911314459171265759173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150437096838557790042024461 56413911314459171265759173)
                ·
                  refine ⟨10577608371461094612329845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56413911314459171265759173 10577608371461094612329845)
                  ·
                    refine ⟨991650784824477619905923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10577608371461094612329845 991650784824477619905923)
                    ·
                      rfl

theorem cell23_5793699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 5].length) (baseStart_5793699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793699 prefixEnd_5793699 := by exact prefixLift 5793699
  have htrace : WordTrace (prefixWord ++ tailWord_5793699) baseStart_5793699 baseEnd_5793699 := by
    simpa [prefixWord, tailWord_5793699, baseEnd_5793699] using wordTrace_append hprefix tailTrace_5793699
  have hstable : (prefixWord ++ tailWord_5793699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793699).length < 2 ^ (prefixWord ++ tailWord_5793699).sum := by decide
  have hdescent : baseEnd_5793699 < baseStart_5793699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793703 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 5]
def baseStart_5793703 : Nat := 118140960795 + 5793703 * 2 ^ 59
def prefixEnd_5793703 : Nat := 4983230072969 + 3 ^ 40 * 5793703 * 2
def baseEnd_5793703 : Nat := 330550489821783427118639

theorem tailTrace_5793703 : CollatzResearch.WordTrace tailWord_5793703 prefixEnd_5793703 330550489821783427118639 := by
  unfold tailWord_5793703
  simp only [CollatzResearch.WordTrace]
  refine ⟨211313708529410991540529763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140875805686273994360353175 211313708529410991540529763)
  ·
    refine ⟨316970562794116487310794645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211313708529410991540529763 316970562794116487310794645)
    ·
      refine ⟨14857995130974210342693499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 316970562794116487310794645 14857995130974210342693499)
      ·
        refine ⟨22286992696461315514040249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14857995130974210342693499 22286992696461315514040249)
        ·
          refine ⟨16715244522345986635530187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22286992696461315514040249 16715244522345986635530187)
          ·
            refine ⟨25072866783518979953295281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16715244522345986635530187 25072866783518979953295281)
            ·
              refine ⟨18804650087639234964971461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25072866783518979953295281 18804650087639234964971461)
              ·
                refine ⟨3525871891432356555932149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18804650087639234964971461 3525871891432356555932149)
                ·
                  refine ⟨330550489821783427118639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3525871891432356555932149 330550489821783427118639)
                  ·
                    rfl

theorem cell23_5793703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 5].length) (baseStart_5793703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793703 prefixEnd_5793703 := by exact prefixLift 5793703
  have htrace : WordTrace (prefixWord ++ tailWord_5793703) baseStart_5793703 baseEnd_5793703 := by
    simpa [prefixWord, tailWord_5793703, baseEnd_5793703] using wordTrace_append hprefix tailTrace_5793703
  have hstable : (prefixWord ++ tailWord_5793703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793703).length < 2 ^ (prefixWord ++ tailWord_5793703).sum := by decide
  have hdescent : baseEnd_5793703 < baseStart_5793703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793736 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_5793736 : Nat := 118140960795 + 5793736 * 2 ^ 59
def prefixEnd_5793736 : Nat := 4983230072969 + 3 ^ 40 * 5793736 * 2
def baseEnd_5793736 : Nat := 2974971353257649214955099

theorem tailTrace_5793736 : CollatzResearch.WordTrace tailWord_5793736 prefixEnd_5793736 2974971353257649214955099 := by
  unfold tailWord_5793736
  simp only [CollatzResearch.WordTrace]
  refine ⟨105657456069145719088240531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140876608092194292117654041 105657456069145719088240531)
  ·
    refine ⟨158486184103718578632360797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105657456069145719088240531 158486184103718578632360797)
    ·
      refine ⟨59432319038894466987135299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158486184103718578632360797 59432319038894466987135299)
      ·
        refine ⟨89148478558341700480702949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59432319038894466987135299 89148478558341700480702949)
        ·
          refine ⟨16715339729689068840131803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89148478558341700480702949 16715339729689068840131803)
          ·
            refine ⟨25073009594533603260197705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16715339729689068840131803 25073009594533603260197705)
            ·
              refine ⟨18804757195900202445148279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25073009594533603260197705 18804757195900202445148279)
              ·
                refine ⟨28207135793850303667722419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18804757195900202445148279 28207135793850303667722419)
                ·
                  refine ⟨42310703690775455501583629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28207135793850303667722419 42310703690775455501583629)
                  ·
                    refine ⟨15866513884040795813093861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42310703690775455501583629 15866513884040795813093861)
                    ·
                      refine ⟨2974971353257649214955099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15866513884040795813093861 2974971353257649214955099)
                      ·
                        rfl

theorem cell23_5793736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_5793736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793736 prefixEnd_5793736 := by exact prefixLift 5793736
  have htrace : WordTrace (prefixWord ++ tailWord_5793736) baseStart_5793736 baseEnd_5793736 := by
    simpa [prefixWord, tailWord_5793736, baseEnd_5793736] using wordTrace_append hprefix tailTrace_5793736
  have hstable : (prefixWord ++ tailWord_5793736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793736).length < 2 ^ (prefixWord ++ tailWord_5793736).sum := by decide
  have hdescent : baseEnd_5793736 < baseStart_5793736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793750 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5793750 : Nat := 118140960795 + 5793750 * 2 ^ 59
def prefixEnd_5793750 : Nat := 4983230072969 + 3 ^ 40 * 5793750 * 2
def baseEnd_5793750 : Nat := 991659513995604053393345

theorem tailTrace_5793750 : CollatzResearch.WordTrace tailWord_5793750 prefixEnd_5793750 991659513995604053393345 := by
  unfold tailWord_5793750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13207213922515044910468169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140876948506827145711660469 13207213922515044910468169)
  ·
    refine ⟨9905410441886283682851127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13207213922515044910468169 9905410441886283682851127)
    ·
      refine ⟨14858115662829425524276691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9905410441886283682851127 14858115662829425524276691)
      ·
        refine ⟨22287173494244138286415037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14858115662829425524276691 22287173494244138286415037)
        ·
          refine ⟨8357690060341551857405639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22287173494244138286415037 8357690060341551857405639)
          ·
            refine ⟨12536535090512327786108459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357690060341551857405639 12536535090512327786108459)
            ·
              refine ⟨18804802635768491679162689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12536535090512327786108459 18804802635768491679162689)
              ·
                refine ⟨14103601976826368759372017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18804802635768491679162689 14103601976826368759372017)
                ·
                  refine ⟨10577701482619776569529013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14103601976826368759372017 10577701482619776569529013)
                  ·
                    refine ⟨991659513995604053393345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10577701482619776569529013 991659513995604053393345)
                    ·
                      rfl

theorem cell23_5793750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5793750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793750 prefixEnd_5793750 := by exact prefixLift 5793750
  have htrace : WordTrace (prefixWord ++ tailWord_5793750) baseStart_5793750 baseEnd_5793750 := by
    simpa [prefixWord, tailWord_5793750, baseEnd_5793750] using wordTrace_append hprefix tailTrace_5793750
  have hstable : (prefixWord ++ tailWord_5793750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793750).length < 2 ^ (prefixWord ++ tailWord_5793750).sum := by decide
  have hdescent : baseEnd_5793750 < baseStart_5793750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793753 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_5793753 : Nat := 118140960795 + 5793753 * 2 ^ 59
def prefixEnd_5793753 : Nat := 4983230072969 + 3 ^ 40 * 5793753 * 2
def baseEnd_5793753 : Nat := 2974980082428775648442521

theorem tailTrace_5793753 : CollatzResearch.WordTrace tailWord_5793753 prefixEnd_5793753 2974980082428775648442521 := by
  unfold tailWord_5793753
  simp only [CollatzResearch.WordTrace]
  refine ⟨211315532179229850079849913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140877021452819900053233275 211315532179229850079849913)
  ·
    refine ⟨158486649134422387559887435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211315532179229850079849913 158486649134422387559887435)
    ·
      refine ⟨237729973701633581339831153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158486649134422387559887435 237729973701633581339831153)
      ·
        refine ⟨178297480276225186004873365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237729973701633581339831153 178297480276225186004873365)
        ·
          refine ⟨8357694387948055593978439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178297480276225186004873365 8357694387948055593978439)
          ·
            refine ⟨12536541581922083390967659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357694387948055593978439 12536541581922083390967659)
            ·
              refine ⟨18804812372883125086451489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12536541581922083390967659 18804812372883125086451489)
              ·
                refine ⟨14103609279662343814838617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18804812372883125086451489 14103609279662343814838617)
                ·
                  refine ⟨10577706959746757861128963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14103609279662343814838617 10577706959746757861128963)
                  ·
                    refine ⟨15866560439620136791693445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10577706959746757861128963 15866560439620136791693445)
                    ·
                      refine ⟨2974980082428775648442521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15866560439620136791693445 2974980082428775648442521)
                      ·
                        rfl

theorem cell23_5793753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_5793753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793753 prefixEnd_5793753 := by exact prefixLift 5793753
  have htrace : WordTrace (prefixWord ++ tailWord_5793753) baseStart_5793753 baseEnd_5793753 := by
    simpa [prefixWord, tailWord_5793753, baseEnd_5793753] using wordTrace_append hprefix tailTrace_5793753
  have hstable : (prefixWord ++ tailWord_5793753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793753).length < 2 ^ (prefixWord ++ tailWord_5793753).sum := by decide
  have hdescent : baseEnd_5793753 < baseStart_5793753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793763 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 3, 4]
def baseStart_5793763 : Nat := 118140960795 + 5793763 * 2 ^ 59
def prefixEnd_5793763 : Nat := 4983230072969 + 3 ^ 40 * 5793763 * 2
def baseEnd_5793763 : Nat := 991661739078440203105825

theorem tailTrace_5793763 : CollatzResearch.WordTrace tailWord_5793763 prefixEnd_5793763 991661739078440203105825 := by
  unfold tailWord_5793763
  simp only [CollatzResearch.WordTrace]
  refine ⟨211315896909193621787713943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140877264606129081191809295 211315896909193621787713943)
  ·
    refine ⟨316973845363790432681570915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211315896909193621787713943 316973845363790432681570915)
    ·
      refine ⟨475460768045685649022356373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316973845363790432681570915 475460768045685649022356373)
      ·
        refine ⟨22287223502141514797922955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 475460768045685649022356373 22287223502141514797922955)
        ·
          refine ⟨33430835253212272196884433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287223502141514797922955 33430835253212272196884433)
          ·
            refine ⟨25073126439909204147663325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33430835253212272196884433 25073126439909204147663325)
            ·
              refine ⟨9402422414965951555373747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25073126439909204147663325 9402422414965951555373747)
              ·
                refine ⟨14103633622448927333060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402422414965951555373747 14103633622448927333060621)
                ·
                  refine ⟨5288862608418347749897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14103633622448927333060621 5288862608418347749897733)
                  ·
                    refine ⟨991661739078440203105825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288862608418347749897733 991661739078440203105825)
                    ·
                      rfl

theorem cell23_5793763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 4].length) (baseStart_5793763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793763 prefixEnd_5793763 := by exact prefixLift 5793763
  have htrace : WordTrace (prefixWord ++ tailWord_5793763) baseStart_5793763 baseEnd_5793763 := by
    simpa [prefixWord, tailWord_5793763, baseEnd_5793763] using wordTrace_append hprefix tailTrace_5793763
  have hstable : (prefixWord ++ tailWord_5793763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793763).length < 2 ^ (prefixWord ++ tailWord_5793763).sum := by decide
  have hdescent : baseEnd_5793763 < baseStart_5793763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793779 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_5793779 : Nat := 118140960795 + 5793779 * 2 ^ 59
def prefixEnd_5793779 : Nat := 4983230072969 + 3 ^ 40 * 5793779 * 2
def baseEnd_5793779 : Nat := 2974993432925792546717401

theorem tailTrace_5793779 : CollatzResearch.WordTrace tailWord_5793779 prefixEnd_5793779 2974993432925792546717401 := by
  unfold tailWord_5793779
  simp only [CollatzResearch.WordTrace]
  refine ⟨211316480477135656520296391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140877653651423771013530927 211316480477135656520296391)
  ·
    refine ⟨316974720715703484780444587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211316480477135656520296391 316974720715703484780444587)
    ·
      refine ⟨475462081073555227170666881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316974720715703484780444587 475462081073555227170666881)
      ·
        refine ⟨356596560805166420378000161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475462081073555227170666881 356596560805166420378000161)
        ·
          refine ⟨267447420603874815283500121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356596560805166420378000161 267447420603874815283500121)
          ·
            refine ⟨200585565452906111462625091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267447420603874815283500121 200585565452906111462625091)
            ·
              refine ⟨300878348179359167193937637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200585565452906111462625091 300878348179359167193937637)
              ·
                refine ⟨56414690283629843848863307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300878348179359167193937637 56414690283629843848863307)
                ·
                  refine ⟨84622035425444765773294961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56414690283629843848863307 84622035425444765773294961)
                  ·
                    refine ⟨63466526569083574329971221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84622035425444765773294961 63466526569083574329971221)
                    ·
                      refine ⟨2974993432925792546717401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63466526569083574329971221 2974993432925792546717401)
                      ·
                        rfl

theorem cell23_5793779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_5793779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793779 prefixEnd_5793779 := by exact prefixLift 5793779
  have htrace : WordTrace (prefixWord ++ tailWord_5793779) baseStart_5793779 baseEnd_5793779 := by
    simpa [prefixWord, tailWord_5793779, baseEnd_5793779] using wordTrace_append hprefix tailTrace_5793779
  have hstable : (prefixWord ++ tailWord_5793779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793779).length < 2 ^ (prefixWord ++ tailWord_5793779).sum := by decide
  have hdescent : baseEnd_5793779 < baseStart_5793779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793790 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5793790 : Nat := 118140960795 + 5793790 * 2 ^ 59
def prefixEnd_5793790 : Nat := 4983230072969 + 3 ^ 40 * 5793790 * 2
def baseEnd_5793790 : Nat := 2974999081212992003679851

theorem tailTrace_5793790 : CollatzResearch.WordTrace tailWord_5793790 prefixEnd_5793790 2974999081212992003679851 := by
  unfold tailWord_5793790
  simp only [CollatzResearch.WordTrace]
  refine ⟨26414610210011975674868353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140877921120063870265964549 26414610210011975674868353)
  ·
    refine ⟨19810957657508981756151265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26414610210011975674868353 19810957657508981756151265)
    ·
      refine ⟨14858218243131736317113449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19810957657508981756151265 14858218243131736317113449)
      ·
        refine ⟨11143663682348802237835087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14858218243131736317113449 11143663682348802237835087)
        ·
          refine ⟨16715495523523203356752631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143663682348802237835087 16715495523523203356752631)
          ·
            refine ⟨25073243285284805035128947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16715495523523203356752631 25073243285284805035128947)
            ·
              refine ⟨37609864927927207552693421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25073243285284805035128947 37609864927927207552693421)
              ·
                refine ⟨14103699347972702832260033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37609864927927207552693421 14103699347972702832260033)
                ·
                  refine ⟨10577774510979527124195025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14103699347972702832260033 10577774510979527124195025)
                  ·
                    refine ⟨7933330883234645343146269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10577774510979527124195025 7933330883234645343146269)
                    ·
                      refine ⟨2974999081212992003679851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7933330883234645343146269 2974999081212992003679851)
                      ·
                        rfl

theorem cell23_5793790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5793790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793790 prefixEnd_5793790 := by exact prefixLift 5793790
  have htrace : WordTrace (prefixWord ++ tailWord_5793790) baseStart_5793790 baseEnd_5793790 := by
    simpa [prefixWord, tailWord_5793790, baseEnd_5793790] using wordTrace_append hprefix tailTrace_5793790
  have hstable : (prefixWord ++ tailWord_5793790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793790).length < 2 ^ (prefixWord ++ tailWord_5793790).sum := by decide
  have hdescent : baseEnd_5793790 < baseStart_5793790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793853 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_5793853 : Nat := 118140960795 + 5793853 * 2 ^ 59
def prefixEnd_5793853 : Nat := 4983230072969 + 3 ^ 40 * 5793853 * 2
def baseEnd_5793853 : Nat := 991677143498075085730687

theorem tailTrace_5793853 : CollatzResearch.WordTrace tailWord_5793853 prefixEnd_5793853 991677143498075085730687 := by
  unfold tailWord_5793853
  simp only [CollatzResearch.WordTrace]
  refine ⟨211319179478867567158490213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140879452985911711438993475 211319179478867567158490213)
  ·
    refine ⟨39622346152287668842216915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211319179478867567158490213 39622346152287668842216915)
    ·
      refine ⟨59433519228431503263325373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39622346152287668842216915 59433519228431503263325373)
      ·
        refine ⟨22287569710661813723747015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59433519228431503263325373 22287569710661813723747015)
        ·
          refine ⟨33431354565992720585620523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287569710661813723747015 33431354565992720585620523)
          ·
            refine ⟨50147031848989080878430785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33431354565992720585620523 50147031848989080878430785)
            ·
              refine ⟨37610273886741810658823089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50147031848989080878430785 37610273886741810658823089)
              ·
                refine ⟨28207705415056357994117317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37610273886741810658823089 28207705415056357994117317)
                ·
                  refine ⟨5288944765323067123896997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28207705415056357994117317 5288944765323067123896997)
                  ·
                    refine ⟨991677143498075085730687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288944765323067123896997 991677143498075085730687)
                    ·
                      rfl

theorem cell23_5793853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_5793853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793853 prefixEnd_5793853 := by exact prefixLift 5793853
  have htrace : WordTrace (prefixWord ++ tailWord_5793853) baseStart_5793853 baseEnd_5793853 := by
    simpa [prefixWord, tailWord_5793853, baseEnd_5793853] using wordTrace_append hprefix tailTrace_5793853
  have hstable : (prefixWord ++ tailWord_5793853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793853).length < 2 ^ (prefixWord ++ tailWord_5793853).sum := by decide
  have hdescent : baseEnd_5793853 < baseStart_5793853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793857 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5793857 : Nat := 118140960795 + 5793857 * 2 ^ 59
def prefixEnd_5793857 : Nat := 4983230072969 + 3 ^ 40 * 5793857 * 2
def baseEnd_5793857 : Nat := 991677828138947747180681

theorem tailTrace_5793857 : CollatzResearch.WordTrace tailWord_5793857 prefixEnd_5793857 991677828138947747180681 := by
  unfold tailWord_5793857
  simp only [CollatzResearch.WordTrace]
  refine ⟨211319325370853075841635825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140879550247235383894423883 211319325370853075841635825)
  ·
    refine ⟨158489494028139806881226869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211319325370853075841635825 158489494028139806881226869)
    ·
      refine ⟨14858390065138106895115019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158489494028139806881226869 14858390065138106895115019)
      ·
        refine ⟨22287585097707160342672529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14858390065138106895115019 22287585097707160342672529)
        ·
          refine ⟨16715688823280370257004397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22287585097707160342672529 16715688823280370257004397)
          ·
            refine ⟨6268383308730138846376649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16715688823280370257004397 6268383308730138846376649)
            ·
              refine ⟨4701287481547604134782487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6268383308730138846376649 4701287481547604134782487)
              ·
                refine ⟨7051931222321406202173731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701287481547604134782487 7051931222321406202173731)
                ·
                  refine ⟨10577896833482109303260597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7051931222321406202173731 10577896833482109303260597)
                  ·
                    refine ⟨991677828138947747180681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10577896833482109303260597 991677828138947747180681)
                    ·
                      rfl

theorem cell23_5793857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5793857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793857 prefixEnd_5793857 := by exact prefixLift 5793857
  have htrace : WordTrace (prefixWord ++ tailWord_5793857) baseStart_5793857 baseEnd_5793857 := by
    simpa [prefixWord, tailWord_5793857, baseEnd_5793857] using wordTrace_append hprefix tailTrace_5793857
  have hstable : (prefixWord ++ tailWord_5793857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793857).length < 2 ^ (prefixWord ++ tailWord_5793857).sum := by decide
  have hdescent : baseEnd_5793857 < baseStart_5793857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793870 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_5793870 : Nat := 118140960795 + 5793870 * 2 ^ 59
def prefixEnd_5793870 : Nat := 4983230072969 + 3 ^ 40 * 5793870 * 2
def baseEnd_5793870 : Nat := 991680053221783896893161

theorem tailTrace_5793870 : CollatzResearch.WordTrace tailWord_5793870 prefixEnd_5793870 991680053221783896893161 := by
  unfold tailWord_5793870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26414974939975747382732383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140879866346537319374572709 26414974939975747382732383)
  ·
    refine ⟨39622462409963621074098575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26414974939975747382732383 39622462409963621074098575)
    ·
      refine ⟨59433693614945431611147863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39622462409963621074098575 59433693614945431611147863)
      ·
        refine ⟨89150540422418147416721795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59433693614945431611147863 89150540422418147416721795)
        ·
          refine ⟨133725810633627221125082693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89150540422418147416721795 133725810633627221125082693)
          ·
            refine ⟨25073589493805103960953005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133725810633627221125082693 25073589493805103960953005)
            ·
              refine ⟨9402596060176913985357377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25073589493805103960953005 9402596060176913985357377)
              ·
                refine ⟨7051947045132685489018033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9402596060176913985357377 7051947045132685489018033)
                ·
                  refine ⟨5288960283849514116763525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7051947045132685489018033 5288960283849514116763525)
                  ·
                    refine ⟨991680053221783896893161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5288960283849514116763525 991680053221783896893161)
                    ·
                      rfl

theorem cell23_5793870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_5793870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793870 prefixEnd_5793870 := by exact prefixLift 5793870
  have htrace : WordTrace (prefixWord ++ tailWord_5793870) baseStart_5793870 baseEnd_5793870 := by
    simpa [prefixWord, tailWord_5793870, baseEnd_5793870] using wordTrace_append hprefix tailTrace_5793870
  have hstable : (prefixWord ++ tailWord_5793870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793870).length < 2 ^ (prefixWord ++ tailWord_5793870).sum := by decide
  have hdescent : baseEnd_5793870 < baseStart_5793870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793876 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5793876 : Nat := 118140960795 + 5793876 * 2 ^ 59
def prefixEnd_5793876 : Nat := 4983230072969 + 3 ^ 40 * 5793876 * 2
def baseEnd_5793876 : Nat := 2975043240549278667204455

theorem tailTrace_5793876 : CollatzResearch.WordTrace tailWord_5793876 prefixEnd_5793876 2975043240549278667204455 := by
  unfold tailWord_5793876
  simp only [CollatzResearch.WordTrace]
  refine ⟨105660009178892121043288741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140880012238522828057718321 105660009178892121043288741)
  ·
    refine ⟨19811251721042272695616639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105660009178892121043288741 19811251721042272695616639)
    ·
      refine ⟨29716877581563409043424959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19811251721042272695616639 29716877581563409043424959)
      ·
        refine ⟨44575316372345113565137439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29716877581563409043424959 44575316372345113565137439)
        ·
          refine ⟨66862974558517670347706159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44575316372345113565137439 66862974558517670347706159)
          ·
            refine ⟨100294461837776505521559239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66862974558517670347706159 100294461837776505521559239)
            ·
              refine ⟨150441692756664758282338859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100294461837776505521559239 150441692756664758282338859)
              ·
                refine ⟨225662539134997137423508289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150441692756664758282338859 225662539134997137423508289)
                ·
                  refine ⟨169246904351247853067631217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225662539134997137423508289 169246904351247853067631217)
                  ·
                    refine ⟨126935178263435889800723413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169246904351247853067631217 126935178263435889800723413)
                    ·
                      refine ⟨2975043240549278667204455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126935178263435889800723413 2975043240549278667204455)
                      ·
                        rfl

theorem cell23_5793876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5793876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793876 prefixEnd_5793876 := by exact prefixLift 5793876
  have htrace : WordTrace (prefixWord ++ tailWord_5793876) baseStart_5793876 baseEnd_5793876 := by
    simpa [prefixWord, tailWord_5793876, baseEnd_5793876] using wordTrace_append hprefix tailTrace_5793876
  have hstable : (prefixWord ++ tailWord_5793876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793876).length < 2 ^ (prefixWord ++ tailWord_5793876).sum := by decide
  have hdescent : baseEnd_5793876 < baseStart_5793876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793877 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5793877 : Nat := 118140960795 + 5793877 * 2 ^ 59
def prefixEnd_5793877 : Nat := 4983230072969 + 3 ^ 40 * 5793877 * 2
def baseEnd_5793877 : Nat := 2975043754029933163291951

theorem tailTrace_5793877 : CollatzResearch.WordTrace tailWord_5793877 prefixEnd_5793877 2975043754029933163291951 := by
  unfold tailWord_5793877
  simp only [CollatzResearch.WordTrace]
  refine ⟨211320054830780619257363885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140880036553853746171575923 211320054830780619257363885)
  ·
    refine ⟨79245020561542732221511457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211320054830780619257363885 79245020561542732221511457)
    ·
      refine ⟨59433765421157049166133593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79245020561542732221511457 59433765421157049166133593)
      ·
        refine ⟨44575324065867786874600195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59433765421157049166133593 44575324065867786874600195)
        ·
          refine ⟨66862986098801680311900293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44575324065867786874600195 66862986098801680311900293)
          ·
            refine ⟨12536809893525315058481305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66862986098801680311900293 12536809893525315058481305)
            ·
              refine ⟨9402607420143986293860979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12536809893525315058481305 9402607420143986293860979)
              ·
                refine ⟨14103911130215979440791469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402607420143986293860979 14103911130215979440791469)
                ·
                  refine ⟨5288966673830992290296801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14103911130215979440791469 5288966673830992290296801)
                  ·
                    refine ⟨3966725005373244217722601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5288966673830992290296801 3966725005373244217722601)
                    ·
                      refine ⟨2975043754029933163291951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966725005373244217722601 2975043754029933163291951)
                      ·
                        rfl

theorem cell23_5793877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5793877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793877 prefixEnd_5793877 := by exact prefixLift 5793877
  have htrace : WordTrace (prefixWord ++ tailWord_5793877) baseStart_5793877 baseEnd_5793877 := by
    simpa [prefixWord, tailWord_5793877, baseEnd_5793877] using wordTrace_append hprefix tailTrace_5793877
  have hstable : (prefixWord ++ tailWord_5793877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793877).length < 2 ^ (prefixWord ++ tailWord_5793877).sum := by decide
  have hdescent : baseEnd_5793877 < baseStart_5793877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793890 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5793890 : Nat := 118140960795 + 5793890 * 2 ^ 59
def prefixEnd_5793890 : Nat := 4983230072969 + 3 ^ 40 * 5793890 * 2
def baseEnd_5793890 : Nat := 2975050429278441612429391

theorem tailTrace_5793890 : CollatzResearch.WordTrace tailWord_5793890 prefixEnd_5793890 2975050429278441612429391 := by
  unfold tailWord_5793890
  simp only [CollatzResearch.WordTrace]
  refine ⟨52830132244933380619396781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140880352653155681651724749 52830132244933380619396781)
  ·
    refine ⟨19811299591850017732273793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52830132244933380619396781 19811299591850017732273793)
    ·
      refine ⟨14858474693887513299205345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19811299591850017732273793 14858474693887513299205345)
      ·
        refine ⟨11143856020415634974404009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14858474693887513299205345 11143856020415634974404009)
        ·
          refine ⟨8357892015311726230803007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11143856020415634974404009 8357892015311726230803007)
          ·
            refine ⟨12536838022967589346204511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357892015311726230803007 12536838022967589346204511)
            ·
              refine ⟨18805257034451384019306767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12536838022967589346204511 18805257034451384019306767)
              ·
                refine ⟨28207885551677076028960151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18805257034451384019306767 28207885551677076028960151)
                ·
                  refine ⟨42311828327515614043440227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28207885551677076028960151 42311828327515614043440227)
                  ·
                    refine ⟨63467742491273421065160341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42311828327515614043440227 63467742491273421065160341)
                    ·
                      refine ⟨2975050429278441612429391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63467742491273421065160341 2975050429278441612429391)
                      ·
                        rfl

theorem cell23_5793890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5793890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793890 prefixEnd_5793890 := by exact prefixLift 5793890
  have htrace : WordTrace (prefixWord ++ tailWord_5793890) baseStart_5793890 baseEnd_5793890 := by
    simpa [prefixWord, tailWord_5793890, baseEnd_5793890] using wordTrace_append hprefix tailTrace_5793890
  have hstable : (prefixWord ++ tailWord_5793890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793890).length < 2 ^ (prefixWord ++ tailWord_5793890).sum := by decide
  have hdescent : baseEnd_5793890 < baseStart_5793890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793936 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_5793936 : Nat := 118140960795 + 5793936 * 2 ^ 59
def prefixEnd_5793936 : Nat := 4983230072969 + 3 ^ 40 * 5793936 * 2
def baseEnd_5793936 : Nat := 2975074049388548432454179

theorem tailTrace_5793936 : CollatzResearch.WordTrace tailWord_5793936 prefixEnd_5793936 2975074049388548432454179 := by
  unfold tailWord_5793936
  simp only [CollatzResearch.WordTrace]
  refine ⟨105661103368783436166880831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140881471158377914889174441 105661103368783436166880831)
  ·
    refine ⟨158491655053175154250321247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105661103368783436166880831 158491655053175154250321247)
    ·
      refine ⟨237737482579762731375481871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158491655053175154250321247 237737482579762731375481871)
      ·
        refine ⟨356606223869644097063222807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237737482579762731375481871 356606223869644097063222807)
        ·
          refine ⟨534909335804466145594834211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356606223869644097063222807 534909335804466145594834211)
          ·
            refine ⟨802364003706699218392251317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534909335804466145594834211 802364003706699218392251317)
            ·
              refine ⟨75221625347503051724273561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 802364003706699218392251317 75221625347503051724273561)
              ·
                refine ⟨56416219010627288793205171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75221625347503051724273561 56416219010627288793205171)
                ·
                  refine ⟨84624328515940933189807757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56416219010627288793205171 84624328515940933189807757)
                  ·
                    refine ⟨31734123193477849946177909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84624328515940933189807757 31734123193477849946177909)
                    ·
                      refine ⟨2975074049388548432454179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31734123193477849946177909 2975074049388548432454179)
                      ·
                        rfl

theorem cell23_5793936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_5793936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793936 prefixEnd_5793936 := by exact prefixLift 5793936
  have htrace : WordTrace (prefixWord ++ tailWord_5793936) baseStart_5793936 baseEnd_5793936 := by
    simpa [prefixWord, tailWord_5793936, baseEnd_5793936] using wordTrace_append hprefix tailTrace_5793936
  have hstable : (prefixWord ++ tailWord_5793936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793936).length < 2 ^ (prefixWord ++ tailWord_5793936).sum := by decide
  have hdescent : baseEnd_5793936 < baseStart_5793936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793953 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5793953 : Nat := 118140960795 + 5793953 * 2 ^ 59
def prefixEnd_5793953 : Nat := 4983230072969 + 3 ^ 40 * 5793953 * 2
def baseEnd_5793953 : Nat := 2975082778559674865941601

theorem tailTrace_5793953 : CollatzResearch.WordTrace tailWord_5793953 prefixEnd_5793953 2975082778559674865941601 := by
  unfold tailWord_5793953
  simp only [CollatzResearch.WordTrace]
  refine ⟨211322826778505284237130513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140881884519003522824753675 211322826778505284237130513)
  ·
    refine ⟨158492120083878963177847885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211322826778505284237130513 158492120083878963177847885)
    ·
      refine ⟨59434545031454611191692957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158492120083878963177847885 59434545031454611191692957)
      ·
        refine ⟨22287954386795479196884859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59434545031454611191692957 22287954386795479196884859)
        ·
          refine ⟨33431931580193218795327289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287954386795479196884859 33431931580193218795327289)
          ·
            refine ⟨25073948685144914096495467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33431931580193218795327289 25073948685144914096495467)
            ·
              refine ⟨37610923027717371144743201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25073948685144914096495467 37610923027717371144743201)
              ·
                refine ⟨28208192270788028358557401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37610923027717371144743201 28208192270788028358557401)
                ·
                  refine ⟨21156144203091021268918051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28208192270788028358557401 21156144203091021268918051)
                  ·
                    refine ⟨31734216304636531903377077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21156144203091021268918051 31734216304636531903377077)
                    ·
                      refine ⟨2975082778559674865941601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31734216304636531903377077 2975082778559674865941601)
                      ·
                        rfl

theorem cell23_5793953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5793953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793953 prefixEnd_5793953 := by exact prefixLift 5793953
  have htrace : WordTrace (prefixWord ++ tailWord_5793953) baseStart_5793953 baseEnd_5793953 := by
    simpa [prefixWord, tailWord_5793953, baseEnd_5793953] using wordTrace_append hprefix tailTrace_5793953
  have hstable : (prefixWord ++ tailWord_5793953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793953).length < 2 ^ (prefixWord ++ tailWord_5793953).sum := by decide
  have hdescent : baseEnd_5793953 < baseStart_5793953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793954 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5793954 : Nat := 118140960795 + 5793954 * 2 ^ 59
def prefixEnd_5793954 : Nat := 4983230072969 + 3 ^ 40 * 5793954 * 2
def baseEnd_5793954 : Nat := 2975083292040329362029097

theorem tailTrace_5793954 : CollatzResearch.WordTrace tailWord_5793954 prefixEnd_5793954 2975083292040329362029097 := by
  unfold tailWord_5793954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52830715812875415351979229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140881908834334440938611277 52830715812875415351979229)
  ·
    refine ⟨19811518429828280756992211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52830715812875415351979229 19811518429828280756992211)
    ·
      refine ⟨29717277644742421135488317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19811518429828280756992211 29717277644742421135488317)
      ·
        refine ⟨11143979116778407925808119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29717277644742421135488317 11143979116778407925808119)
        ·
          refine ⟨16715968675167611888712179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143979116778407925808119 16715968675167611888712179)
          ·
            refine ⟨25073953012751417833068269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16715968675167611888712179 25073953012751417833068269)
            ·
              refine ⟨9402732379781781687400601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25073953012751417833068269 9402732379781781687400601)
              ·
                refine ⟨7052049284836336265550451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9402732379781781687400601 7052049284836336265550451)
                ·
                  refine ⟨10578073927254504398325677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052049284836336265550451 10578073927254504398325677)
                  ·
                    refine ⟨3966777722720439149372129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10578073927254504398325677 3966777722720439149372129)
                    ·
                      refine ⟨2975083292040329362029097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966777722720439149372129 2975083292040329362029097)
                      ·
                        rfl

theorem cell23_5793954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5793954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793954 prefixEnd_5793954 := by exact prefixLift 5793954
  have htrace : WordTrace (prefixWord ++ tailWord_5793954) baseStart_5793954 baseEnd_5793954 := by
    simpa [prefixWord, tailWord_5793954, baseEnd_5793954] using wordTrace_append hprefix tailTrace_5793954
  have hstable : (prefixWord ++ tailWord_5793954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793954).length < 2 ^ (prefixWord ++ tailWord_5793954).sum := by decide
  have hdescent : baseEnd_5793954 < baseStart_5793954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793983 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_5793983 : Nat := 118140960795 + 5793983 * 2 ^ 59
def prefixEnd_5793983 : Nat := 4983230072969 + 3 ^ 40 * 5793983 * 2
def baseEnd_5793983 : Nat := 2975098182979309748566463

theorem tailTrace_5793983 : CollatzResearch.WordTrace tailWord_5793983 prefixEnd_5793983 2975098182979309748566463 := by
  unfold tailWord_5793983
  simp only [CollatzResearch.WordTrace]
  refine ⟨211323920968396599360722603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140882613978931066240481735 211323920968396599360722603)
  ·
    refine ⟨316985881452594899041083905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211323920968396599360722603 316985881452594899041083905)
    ·
      refine ⟨237739411089446174280812929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316985881452594899041083905 237739411089446174280812929)
      ·
        refine ⟨178304558317084630710609697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237739411089446174280812929 178304558317084630710609697)
        ·
          refine ⟨133728418737813473032957273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178304558317084630710609697 133728418737813473032957273)
          ·
            refine ⟨100296314053360104774717955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133728418737813473032957273 100296314053360104774717955)
            ·
              refine ⟨150444471080040157162076933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100296314053360104774717955 150444471080040157162076933)
              ·
                refine ⟨28208338327507529467889425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150444471080040157162076933 28208338327507529467889425)
                ·
                  refine ⟨21156253745630647100917069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28208338327507529467889425 21156253745630647100917069)
                  ·
                    refine ⟨7933595154611492662843901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21156253745630647100917069 7933595154611492662843901)
                    ·
                      refine ⟨2975098182979309748566463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7933595154611492662843901 2975098182979309748566463)
                      ·
                        rfl

theorem cell23_5793983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_5793983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793983 prefixEnd_5793983 := by exact prefixLift 5793983
  have htrace : WordTrace (prefixWord ++ tailWord_5793983) baseStart_5793983 baseEnd_5793983 := by
    simpa [prefixWord, tailWord_5793983, baseEnd_5793983] using wordTrace_append hprefix tailTrace_5793983
  have hstable : (prefixWord ++ tailWord_5793983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793983).length < 2 ^ (prefixWord ++ tailWord_5793983).sum := by decide
  have hdescent : baseEnd_5793983 < baseStart_5793983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5793984 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2]
def baseStart_5793984 : Nat := 118140960795 + 5793984 * 2 ^ 59
def prefixEnd_5793984 : Nat := 4983230072969 + 3 ^ 40 * 5793984 * 2
def baseEnd_5793984 : Nat := 2975098696459964244653959

theorem tailTrace_5793984 : CollatzResearch.WordTrace tailWord_5793984 prefixEnd_5793984 2975098696459964244653959 := by
  unfold tailWord_5793984
  simp only [CollatzResearch.WordTrace]
  refine ⟨105661978720696488265754503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140882638294261984354339337 105661978720696488265754503)
  ·
    refine ⟨158492968081044732398631755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105661978720696488265754503 158492968081044732398631755)
    ·
      refine ⟨237739452121567098597947633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158492968081044732398631755 237739452121567098597947633)
      ·
        refine ⟨178304589091175323948460725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237739452121567098597947633 178304589091175323948460725)
        ·
          refine ⟨16716055227297686620168193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178304589091175323948460725 16716055227297686620168193)
          ·
            refine ⟨12537041420473264965126145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16716055227297686620168193 12537041420473264965126145)
            ·
              refine ⟨9402781065354948723844609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12537041420473264965126145 9402781065354948723844609)
              ·
                refine ⟨7052085799016211542883457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9402781065354948723844609 7052085799016211542883457)
                ·
                  refine ⟨5289064349262158657162593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052085799016211542883457 5289064349262158657162593)
                  ·
                    refine ⟨3966798261946618992871945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5289064349262158657162593 3966798261946618992871945)
                    ·
                      refine ⟨2975098696459964244653959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3966798261946618992871945 2975098696459964244653959)
                      ·
                        rfl

theorem cell23_5793984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_5793984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5793984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5793984 prefixEnd_5793984 := by exact prefixLift 5793984
  have htrace : WordTrace (prefixWord ++ tailWord_5793984) baseStart_5793984 baseEnd_5793984 := by
    simpa [prefixWord, tailWord_5793984, baseEnd_5793984] using wordTrace_append hprefix tailTrace_5793984
  have hstable : (prefixWord ++ tailWord_5793984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5793984).length < 2 ^ (prefixWord ++ tailWord_5793984).sum := by decide
  have hdescent : baseEnd_5793984 < baseStart_5793984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5793984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794063 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 6]
def baseStart_5794063 : Nat := 118140960795 + 5794063 * 2 ^ 59
def prefixEnd_5794063 : Nat := 4983230072969 + 3 ^ 40 * 5794063 * 2
def baseEnd_5794063 : Nat := 330571029047963270618455

theorem tailTrace_5794063 : CollatzResearch.WordTrace tailWord_5794063 prefixEnd_5794063 330571029047963270618455 := by
  unfold tailWord_5794063
  simp only [CollatzResearch.WordTrace]
  refine ⟨211326838808106773023634843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140884559205404515349089895 211326838808106773023634843)
  ·
    refine ⟨316990258212160159535452265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211326838808106773023634843 316990258212160159535452265)
    ·
      refine ⟨237742693659120119651589199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316990258212160159535452265 237742693659120119651589199)
      ·
        refine ⟨356614040488680179477383799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237742693659120119651589199 356614040488680179477383799)
        ·
          refine ⟨534921060733020269216075699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356614040488680179477383799 534921060733020269216075699)
          ·
            refine ⟨802381591099530403824113549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534921060733020269216075699 802381591099530403824113549)
            ·
              refine ⟨300893096662323901434042581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802381591099530403824113549 300893096662323901434042581)
              ·
                refine ⟨7052181953023216439860373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300893096662323901434042581 7052181953023216439860373)
                ·
                  refine ⟨330571029047963270618455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7052181953023216439860373 330571029047963270618455)
                  ·
                    rfl

theorem cell23_5794063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 6].length) (baseStart_5794063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794063 prefixEnd_5794063 := by exact prefixLift 5794063
  have htrace : WordTrace (prefixWord ++ tailWord_5794063) baseStart_5794063 baseEnd_5794063 := by
    simpa [prefixWord, tailWord_5794063, baseEnd_5794063] using wordTrace_append hprefix tailTrace_5794063
  have hstable : (prefixWord ++ tailWord_5794063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794063).length < 2 ^ (prefixWord ++ tailWord_5794063).sum := by decide
  have hdescent : baseEnd_5794063 < baseStart_5794063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794084 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_5794084 : Nat := 118140960795 + 5794084 * 2 ^ 59
def prefixEnd_5794084 : Nat := 4983230072969 + 3 ^ 40 * 5794084 * 2
def baseEnd_5794084 : Nat := 991716681508471284467833

theorem tailTrace_5794084 : CollatzResearch.WordTrace tailWord_5794084 prefixEnd_5794084 991716681508471284467833 := by
  unfold tailWord_5794084
  simp only [CollatzResearch.WordTrace]
  refine ⟨105663802370515346805074653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140885069827353795740099537 105663802370515346805074653)
  ·
    refine ⟨39623925888943255051902995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105663802370515346805074653 39623925888943255051902995)
    ·
      refine ⟨59435888833414882577854493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39623925888943255051902995 59435888833414882577854493)
      ·
        refine ⟨22288458312530580966695435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59435888833414882577854493 22288458312530580966695435)
        ·
          refine ⟨33432687468795871450043153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22288458312530580966695435 33432687468795871450043153)
          ·
            refine ⟨25074515601596903587532365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33432687468795871450043153 25074515601596903587532365)
            ·
              refine ⟨9402943350598838845324637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25074515601596903587532365 9402943350598838845324637)
              ·
                refine ⟨3526103756474564566996739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9402943350598838845324637 3526103756474564566996739)
                ·
                  refine ⟨5289155634711846850495109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526103756474564566996739 5289155634711846850495109)
                  ·
                    refine ⟨991716681508471284467833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289155634711846850495109 991716681508471284467833)
                    ·
                      rfl

theorem cell23_5794084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_5794084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794084 prefixEnd_5794084 := by exact prefixLift 5794084
  have htrace : WordTrace (prefixWord ++ tailWord_5794084) baseStart_5794084 baseEnd_5794084 := by
    simpa [prefixWord, tailWord_5794084, baseEnd_5794084] using wordTrace_append hprefix tailTrace_5794084
  have hstable : (prefixWord ++ tailWord_5794084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794084).length < 2 ^ (prefixWord ++ tailWord_5794084).sum := by decide
  have hdescent : baseEnd_5794084 < baseStart_5794084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794144 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 1, 5]
def baseStart_5794144 : Nat := 118140960795 + 5794144 * 2 ^ 59
def prefixEnd_5794144 : Nat := 4983230072969 + 3 ^ 40 * 5794144 * 2
def baseEnd_5794144 : Nat := 991726951121561206217741

theorem tailTrace_5794144 : CollatzResearch.WordTrace tailWord_5794144 prefixEnd_5794144 991726951121561206217741 := by
  unfold tailWord_5794144
  simp only [CollatzResearch.WordTrace]
  refine ⟨105664896560406661928666743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140886528747208882571555657 105664896560406661928666743)
  ·
    refine ⟨158497344840609992893000115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105664896560406661928666743 158497344840609992893000115)
    ·
      refine ⟨237746017260914989339500173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158497344840609992893000115 237746017260914989339500173)
      ·
        refine ⟨89154756472843121002312565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237746017260914989339500173 89154756472843121002312565)
        ·
          refine ⟨8358258419329042593966803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89154756472843121002312565 8358258419329042593966803)
          ·
            refine ⟨12537387628993563890950205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8358258419329042593966803 12537387628993563890950205)
            ·
              refine ⟨4701520360872586459106327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12537387628993563890950205 4701520360872586459106327)
              ·
                refine ⟨7052280541308879688659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701520360872586459106327 7052280541308879688659491)
                ·
                  refine ⟨10578420811963319532989237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052280541308879688659491 10578420811963319532989237)
                  ·
                    refine ⟨991726951121561206217741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10578420811963319532989237 991726951121561206217741)
                    ·
                      rfl

theorem cell23_5794144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_5794144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794144 prefixEnd_5794144 := by exact prefixLift 5794144
  have htrace : WordTrace (prefixWord ++ tailWord_5794144) baseStart_5794144 baseEnd_5794144 := by
    simpa [prefixWord, tailWord_5794144, baseEnd_5794144] using wordTrace_append hprefix tailTrace_5794144
  have hstable : (prefixWord ++ tailWord_5794144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794144).length < 2 ^ (prefixWord ++ tailWord_5794144).sum := by decide
  have hdescent : baseEnd_5794144 < baseStart_5794144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794177 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5794177 : Nat := 118140960795 + 5794177 * 2 ^ 59
def prefixEnd_5794177 : Nat := 4983230072969 + 3 ^ 40 * 5794177 * 2
def baseEnd_5794177 : Nat := 2975197798226281989540571

theorem tailTrace_5794177 : CollatzResearch.WordTrace tailWord_5794177 prefixEnd_5794177 2975197798226281989540571 := by
  unfold tailWord_5794177
  simp only [CollatzResearch.WordTrace]
  refine ⟨211330996729693770493284785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140887331153129180328856523 211330996729693770493284785)
  ·
    refine ⟨158498247547270327869963589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211330996729693770493284785 158498247547270327869963589)
    ·
      refine ⟨29718421415113186475618173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158498247547270327869963589 29718421415113186475618173)
      ·
        refine ⟨11144408030667444928356815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29718421415113186475618173 11144408030667444928356815)
        ·
          refine ⟨16716612046001167392535223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11144408030667444928356815 16716612046001167392535223)
          ·
            refine ⟨25074918069001751088802835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16716612046001167392535223 25074918069001751088802835)
            ·
              refine ⟨37612377103502626633204253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25074918069001751088802835 37612377103502626633204253)
              ·
                refine ⟨14104641413813484987451595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37612377103502626633204253 14104641413813484987451595)
                ·
                  refine ⟨21156962120720227481177393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14104641413813484987451595 21156962120720227481177393)
                  ·
                    refine ⟨15867721590540170610883045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21156962120720227481177393 15867721590540170610883045)
                    ·
                      refine ⟨2975197798226281989540571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15867721590540170610883045 2975197798226281989540571)
                      ·
                        rfl

theorem cell23_5794177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5794177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794177 prefixEnd_5794177 := by exact prefixLift 5794177
  have htrace : WordTrace (prefixWord ++ tailWord_5794177) baseStart_5794177 baseEnd_5794177 := by
    simpa [prefixWord, tailWord_5794177, baseEnd_5794177] using wordTrace_append hprefix tailTrace_5794177
  have hstable : (prefixWord ++ tailWord_5794177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794177).length < 2 ^ (prefixWord ++ tailWord_5794177).sum := by decide
  have hdescent : baseEnd_5794177 < baseStart_5794177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794197 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_5794197 : Nat := 118140960795 + 5794197 * 2 ^ 59
def prefixEnd_5794197 : Nat := 4983230072969 + 3 ^ 40 * 5794197 * 2
def baseEnd_5794197 : Nat := 2975208067839371911290479

theorem tailTrace_5794197 : CollatzResearch.WordTrace tailWord_5794197 prefixEnd_5794197 2975208067839371911290479 := by
  unfold tailWord_5794197
  simp only [CollatzResearch.WordTrace]
  refine ⟨211331726189621313909012845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140887817459747542606008563 211331726189621313909012845)
  ·
    refine ⟨79249397321107992715879817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211331726189621313909012845 79249397321107992715879817)
    ·
      refine ⟨59437047990830994536909863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79249397321107992715879817 59437047990830994536909863)
      ·
        refine ⟨89155571986246491805364795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59437047990830994536909863 89155571986246491805364795)
        ·
          refine ⟨133733357979369737708047193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89155571986246491805364795 133733357979369737708047193)
          ·
            refine ⟨100300018484527303281035395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133733357979369737708047193 100300018484527303281035395)
            ·
              refine ⟨150450027726790954921553093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100300018484527303281035395 150450027726790954921553093)
              ·
                refine ⟨28209380198773304047791205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150450027726790954921553093 28209380198773304047791205)
                ·
                  refine ⟨5289258787269994508960851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28209380198773304047791205 5289258787269994508960851)
                  ·
                    refine ⟨7933888180904991763441277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5289258787269994508960851 7933888180904991763441277)
                    ·
                      refine ⟨2975208067839371911290479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7933888180904991763441277 2975208067839371911290479)
                      ·
                        rfl

theorem cell23_5794197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_5794197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794197 prefixEnd_5794197 := by exact prefixLift 5794197
  have htrace : WordTrace (prefixWord ++ tailWord_5794197) baseStart_5794197 baseEnd_5794197 := by
    simpa [prefixWord, tailWord_5794197, baseEnd_5794197] using wordTrace_append hprefix tailTrace_5794197
  have hstable : (prefixWord ++ tailWord_5794197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794197).length < 2 ^ (prefixWord ++ tailWord_5794197).sum := by decide
  have hdescent : baseEnd_5794197 < baseStart_5794197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794228 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5794228 : Nat := 118140960795 + 5794228 * 2 ^ 59
def prefixEnd_5794228 : Nat := 4983230072969 + 3 ^ 40 * 5794228 * 2
def baseEnd_5794228 : Nat := 2975223985739661290002837

theorem tailTrace_5794228 : CollatzResearch.WordTrace tailWord_5794228 prefixEnd_5794228 2975223985739661290002837 := by
  unfold tailWord_5794228
  simp only [CollatzResearch.WordTrace]
  refine ⟨105666428426254503101695669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140888571235006004135594225 105666428426254503101695669)
  ·
    refine ⟨9906227664961359665783969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105666428426254503101695669 9906227664961359665783969)
    ·
      refine ⟨7429670748721019749337977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9906227664961359665783969 7429670748721019749337977)
      ·
        refine ⟨5572253061540764812003483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7429670748721019749337977 5572253061540764812003483)
        ·
          refine ⟨8358379592311147218005225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572253061540764812003483 8358379592311147218005225)
          ·
            refine ⟨6268784694233360413503919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8358379592311147218005225 6268784694233360413503919)
            ·
              refine ⟨9403177041350040620255879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268784694233360413503919 9403177041350040620255879)
              ·
                refine ⟨14104765562025060930383819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9403177041350040620255879 14104765562025060930383819)
                ·
                  refine ⟨21157148343037591395575729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14104765562025060930383819 21157148343037591395575729)
                  ·
                    refine ⟨15867861257278193546681797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21157148343037591395575729 15867861257278193546681797)
                    ·
                      refine ⟨2975223985739661290002837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15867861257278193546681797 2975223985739661290002837)
                      ·
                        rfl

theorem cell23_5794228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5794228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794228 prefixEnd_5794228 := by exact prefixLift 5794228
  have htrace : WordTrace (prefixWord ++ tailWord_5794228) baseStart_5794228 baseEnd_5794228 := by
    simpa [prefixWord, tailWord_5794228, baseEnd_5794228] using wordTrace_append hprefix tailTrace_5794228
  have hstable : (prefixWord ++ tailWord_5794228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794228).length < 2 ^ (prefixWord ++ tailWord_5794228).sum := by decide
  have hdescent : baseEnd_5794228 < baseStart_5794228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794231 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_5794231 : Nat := 118140960795 + 5794231 * 2 ^ 59
def prefixEnd_5794231 : Nat := 4983230072969 + 3 ^ 40 * 5794231 * 2
def baseEnd_5794231 : Nat := 2975225526181624778265323

theorem tailTrace_5794231 : CollatzResearch.WordTrace tailWord_5794231 prefixEnd_5794231 2975225526181624778265323 := by
  unfold tailWord_5794231
  simp only [CollatzResearch.WordTrace]
  refine ⟨211332966271498137715750547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140888644180998758477167031 211332966271498137715750547)
  ·
    refine ⟨316999449407247206573625821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211332966271498137715750547 316999449407247206573625821)
    ·
      refine ⟨118874793527717702465109683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316999449407247206573625821 118874793527717702465109683)
      ·
        refine ⟨178312190291576553697664525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118874793527717702465109683 178312190291576553697664525)
        ·
          refine ⟨66867071359341207636624197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178312190291576553697664525 66867071359341207636624197)
          ·
            refine ⟨12537575879876476431867037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66867071359341207636624197 12537575879876476431867037)
            ·
              refine ⟨4701590954953678661950139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12537575879876476431867037 4701590954953678661950139)
              ·
                refine ⟨7052386432430517992925209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701590954953678661950139 7052386432430517992925209)
                ·
                  refine ⟨5289289824322888494693907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052386432430517992925209 5289289824322888494693907)
                  ·
                    refine ⟨7933934736484332742040861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5289289824322888494693907 7933934736484332742040861)
                    ·
                      refine ⟨2975225526181624778265323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7933934736484332742040861 2975225526181624778265323)
                      ·
                        rfl

theorem cell23_5794231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_5794231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794231 prefixEnd_5794231 := by exact prefixLift 5794231
  have htrace : WordTrace (prefixWord ++ tailWord_5794231) baseStart_5794231 baseEnd_5794231 := by
    simpa [prefixWord, tailWord_5794231, baseEnd_5794231] using wordTrace_append hprefix tailTrace_5794231
  have hstable : (prefixWord ++ tailWord_5794231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794231).length < 2 ^ (prefixWord ++ tailWord_5794231).sum := by decide
  have hdescent : baseEnd_5794231 < baseStart_5794231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794240 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_5794240 : Nat := 118140960795 + 5794240 * 2 ^ 59
def prefixEnd_5794240 : Nat := 4983230072969 + 3 ^ 40 * 5794240 * 2
def baseEnd_5794240 : Nat := 2975230147507515243052781

theorem tailTrace_5794240 : CollatzResearch.WordTrace tailWord_5794240 prefixEnd_5794240 2975230147507515243052781 := by
  unfold tailWord_5794240
  simp only [CollatzResearch.WordTrace]
  refine ⟨105666647264232766126414087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140888863018977021501885449 105666647264232766126414087)
  ·
    refine ⟨158499970896349149189621131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105666647264232766126414087 158499970896349149189621131)
    ·
      refine ⟨237749956344523723784431697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158499970896349149189621131 237749956344523723784431697)
      ·
        refine ⟨178312467258392792838323773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237749956344523723784431697 178312467258392792838323773)
        ·
          refine ⟨66867175221897297314371415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178312467258392792838323773 66867175221897297314371415)
          ·
            refine ⟨100300762832845945971557123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66867175221897297314371415 100300762832845945971557123)
            ·
              refine ⟨150451144249268918957335685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100300762832845945971557123 150451144249268918957335685)
              ·
                refine ⟨28209589546737922304500441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150451144249268918957335685 28209589546737922304500441)
                ·
                  refine ⟨21157192160053441728375331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28209589546737922304500441 21157192160053441728375331)
                  ·
                    refine ⟨31735788240080162592562997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21157192160053441728375331 31735788240080162592562997)
                    ·
                      refine ⟨2975230147507515243052781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31735788240080162592562997 2975230147507515243052781)
                      ·
                        rfl

theorem cell23_5794240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_5794240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794240 prefixEnd_5794240 := by exact prefixLift 5794240
  have htrace : WordTrace (prefixWord ++ tailWord_5794240) baseStart_5794240 baseEnd_5794240 := by
    simpa [prefixWord, tailWord_5794240, baseEnd_5794240] using wordTrace_append hprefix tailTrace_5794240
  have hstable : (prefixWord ++ tailWord_5794240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794240).length < 2 ^ (prefixWord ++ tailWord_5794240).sum := by decide
  have hdescent : baseEnd_5794240 < baseStart_5794240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794300 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_5794300 : Nat := 118140960795 + 5794300 * 2 ^ 59
def prefixEnd_5794300 : Nat := 4983230072969 + 3 ^ 40 * 5794300 * 2
def baseEnd_5794300 : Nat := 2975260956346785008302505

theorem tailTrace_5794300 : CollatzResearch.WordTrace tailWord_5794300 prefixEnd_5794300 2975260956346785008302505 := by
  unfold tailWord_5794300
  simp only [CollatzResearch.WordTrace]
  refine ⟨105667741454124081250006177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140890321938832108333341569 105667741454124081250006177)
  ·
    refine ⟨79250806090593060937504633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105667741454124081250006177 79250806090593060937504633)
    ·
      refine ⟨59438104567944795703128475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79250806090593060937504633 59438104567944795703128475)
      ·
        refine ⟨89157156851917193554692713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59438104567944795703128475 89157156851917193554692713)
        ·
          refine ⟨66867867638937895166019535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89157156851917193554692713 66867867638937895166019535)
          ·
            refine ⟨100301801458406842749029303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66867867638937895166019535 100301801458406842749029303)
            ·
              refine ⟨150452702187610264123543955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100301801458406842749029303 150452702187610264123543955)
              ·
                refine ⟨225679053281415396185315933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150452702187610264123543955 225679053281415396185315933)
                ·
                  refine ⟨84629644980530773569493475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225679053281415396185315933 84629644980530773569493475)
                  ·
                    refine ⟨126944467470796160354240213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84629644980530773569493475 126944467470796160354240213)
                    ·
                      refine ⟨2975260956346785008302505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126944467470796160354240213 2975260956346785008302505)
                      ·
                        rfl

theorem cell23_5794300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_5794300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794300 prefixEnd_5794300 := by exact prefixLift 5794300
  have htrace : WordTrace (prefixWord ++ tailWord_5794300) baseStart_5794300 baseEnd_5794300 := by
    simpa [prefixWord, tailWord_5794300, baseEnd_5794300] using wordTrace_append hprefix tailTrace_5794300
  have hstable : (prefixWord ++ tailWord_5794300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794300).length < 2 ^ (prefixWord ++ tailWord_5794300).sum := by decide
  have hdescent : baseEnd_5794300 < baseStart_5794300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794307 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 2, 5]
def baseStart_5794307 : Nat := 118140960795 + 5794307 * 2 ^ 59
def prefixEnd_5794307 : Nat := 4983230072969 + 3 ^ 40 * 5794307 * 2
def baseEnd_5794307 : Nat := 991754850237122160304991

theorem tailTrace_5794307 : CollatzResearch.WordTrace tailWord_5794307 prefixEnd_5794307 991754850237122160304991 := by
  unfold tailWord_5794307
  simp only [CollatzResearch.WordTrace]
  refine ⟨211335738219222802695517175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140890492146148535130344783 211335738219222802695517175)
  ·
    refine ⟨317003607328834204043275763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211335738219222802695517175 317003607328834204043275763)
    ·
      refine ⟨475505410993251306064913645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317003607328834204043275763 475505410993251306064913645)
      ·
        refine ⟨178314529122469239774342617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475505410993251306064913645 178314529122469239774342617)
        ·
          refine ⟨133735896841851929830756963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178314529122469239774342617 133735896841851929830756963)
          ·
            refine ⟨200603845262777894746135445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133735896841851929830756963 200603845262777894746135445)
            ·
              refine ⟨9403305246692713816225099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200603845262777894746135445 9403305246692713816225099)
              ·
                refine ⟨14104957870039070724337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9403305246692713816225099 14104957870039070724337649)
                ·
                  refine ⟨10578718402529303043253237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14104957870039070724337649 10578718402529303043253237)
                  ·
                    refine ⟨991754850237122160304991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10578718402529303043253237 991754850237122160304991)
                    ·
                      rfl

theorem cell23_5794307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 5].length) (baseStart_5794307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794307 prefixEnd_5794307 := by exact prefixLift 5794307
  have htrace : WordTrace (prefixWord ++ tailWord_5794307) baseStart_5794307 baseEnd_5794307 := by
    simpa [prefixWord, tailWord_5794307, baseEnd_5794307] using wordTrace_append hprefix tailTrace_5794307
  have hstable : (prefixWord ++ tailWord_5794307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794307).length < 2 ^ (prefixWord ++ tailWord_5794307).sum := by decide
  have hdescent : baseEnd_5794307 < baseStart_5794307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794347 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3]
def baseStart_5794347 : Nat := 118140960795 + 5794347 * 2 ^ 59
def prefixEnd_5794347 : Nat := 4983230072969 + 3 ^ 40 * 5794347 * 2
def baseEnd_5794347 : Nat := 2975285089937546324414789

theorem tailTrace_5794347 : CollatzResearch.WordTrace tailWord_5794347 prefixEnd_5794347 2975285089937546324414789 := by
  unfold tailWord_5794347
  simp only [CollatzResearch.WordTrace]
  refine ⟨211337197139077889526973295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140891464759385259684648863 211337197139077889526973295)
  ·
    refine ⟨317005795708616834290459943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211337197139077889526973295 317005795708616834290459943)
    ·
      refine ⟨475508693562925251435689915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317005795708616834290459943 475508693562925251435689915)
      ·
        refine ⟨713263040344387877153534873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475508693562925251435689915 713263040344387877153534873)
        ·
          refine ⟨534947280258290907865151155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713263040344387877153534873 534947280258290907865151155)
          ·
            refine ⟨802420920387436361797726733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534947280258290907865151155 802420920387436361797726733)
            ·
              refine ⟨300907845145288635674147525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802420920387436361797726733 300907845145288635674147525)
              ·
                refine ⟨56420220964741619188902661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300907845145288635674147525 56420220964741619188902661)
                ·
                  refine ⟨10578791430889053597919249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56420220964741619188902661 10578791430889053597919249)
                  ·
                    refine ⟨7934093573166790198439437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10578791430889053597919249 7934093573166790198439437)
                    ·
                      refine ⟨2975285089937546324414789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7934093573166790198439437 2975285089937546324414789)
                      ·
                        rfl

theorem cell23_5794347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3].length) (baseStart_5794347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794347 prefixEnd_5794347 := by exact prefixLift 5794347
  have htrace : WordTrace (prefixWord ++ tailWord_5794347) baseStart_5794347 baseEnd_5794347 := by
    simpa [prefixWord, tailWord_5794347, baseEnd_5794347] using wordTrace_append hprefix tailTrace_5794347
  have hstable : (prefixWord ++ tailWord_5794347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794347).length < 2 ^ (prefixWord ++ tailWord_5794347).sum := by decide
  have hdescent : baseEnd_5794347 < baseStart_5794347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794364 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_5794364 : Nat := 118140960795 + 5794364 * 2 ^ 59
def prefixEnd_5794364 : Nat := 4983230072969 + 3 ^ 40 * 5794364 * 2
def baseEnd_5794364 : Nat := 2975293819108672757902211

theorem tailTrace_5794364 : CollatzResearch.WordTrace tailWord_5794364 prefixEnd_5794364 2975293819108672757902211 := by
  unfold tailWord_5794364
  simp only [CollatzResearch.WordTrace]
  refine ⟨105668908590008150715171073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140891878120010867620228097 105668908590008150715171073)
  ·
    refine ⟨79251681442506113036378305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105668908590008150715171073 79251681442506113036378305)
    ·
      refine ⟨59438761081879584777283729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79251681442506113036378305 59438761081879584777283729)
      ·
        refine ⟨44579070811409688582962797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59438761081879584777283729 44579070811409688582962797)
        ·
          refine ⟨16717151554278633218611049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44579070811409688582962797 16717151554278633218611049)
          ·
            refine ⟨12537863665708974913958287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16717151554278633218611049 12537863665708974913958287)
            ·
              refine ⟨18806795498563462370937431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12537863665708974913958287 18806795498563462370937431)
              ·
                refine ⟨28210193247845193556406147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18806795498563462370937431 28210193247845193556406147)
                ·
                  refine ⟨42315289871767790334609221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28210193247845193556406147 42315289871767790334609221)
                  ·
                    refine ⟨7934116850956460687739229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42315289871767790334609221 7934116850956460687739229)
                    ·
                      refine ⟨2975293819108672757902211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7934116850956460687739229 2975293819108672757902211)
                      ·
                        rfl

theorem cell23_5794364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_5794364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794364 prefixEnd_5794364 := by exact prefixLift 5794364
  have htrace : WordTrace (prefixWord ++ tailWord_5794364) baseStart_5794364 baseEnd_5794364 := by
    simpa [prefixWord, tailWord_5794364, baseEnd_5794364] using wordTrace_append hprefix tailTrace_5794364
  have hstable : (prefixWord ++ tailWord_5794364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794364).length < 2 ^ (prefixWord ++ tailWord_5794364).sum := by decide
  have hdescent : baseEnd_5794364 < baseStart_5794364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794404 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_5794404 : Nat := 118140960795 + 5794404 * 2 ^ 59
def prefixEnd_5794404 : Nat := 4983230072969 + 3 ^ 40 * 5794404 * 2
def baseEnd_5794404 : Nat := 2975314358334852601402027

theorem tailTrace_5794404 : CollatzResearch.WordTrace tailWord_5794404 prefixEnd_5794404 2975314358334852601402027 := by
  unfold tailWord_5794404
  simp only [CollatzResearch.WordTrace]
  refine ⟨105669638049935694130899133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140892850733247592174532177 105669638049935694130899133)
  ·
    refine ⟨39626114268725885299087175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105669638049935694130899133 39626114268725885299087175)
    ·
      refine ⟨59439171403088827948630763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39626114268725885299087175 59439171403088827948630763)
      ·
        refine ⟨89158757104633241922946145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59439171403088827948630763 89158757104633241922946145)
        ·
          refine ⟨66869067828474931442209609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89158757104633241922946145 66869067828474931442209609)
          ·
            refine ⟨50151800871356198581657207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66869067828474931442209609 50151800871356198581657207)
            ·
              refine ⟨75227701307034297872485811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50151800871356198581657207 75227701307034297872485811)
              ·
                refine ⟨112841551960551446808728717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75227701307034297872485811 112841551960551446808728717)
                ·
                  refine ⟨42315581985206792553273269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112841551960551446808728717 42315581985206792553273269)
                  ·
                    refine ⟨3967085811113136801869369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42315581985206792553273269 3967085811113136801869369)
                    ·
                      refine ⟨2975314358334852601402027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967085811113136801869369 2975314358334852601402027)
                      ·
                        rfl

theorem cell23_5794404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_5794404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794404 prefixEnd_5794404 := by exact prefixLift 5794404
  have htrace : WordTrace (prefixWord ++ tailWord_5794404) baseStart_5794404 baseEnd_5794404 := by
    simpa [prefixWord, tailWord_5794404, baseEnd_5794404] using wordTrace_append hprefix tailTrace_5794404
  have hstable : (prefixWord ++ tailWord_5794404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794404).length < 2 ^ (prefixWord ++ tailWord_5794404).sum := by decide
  have hdescent : baseEnd_5794404 < baseStart_5794404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794422 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_5794422 : Nat := 118140960795 + 5794422 * 2 ^ 59
def prefixEnd_5794422 : Nat := 4983230072969 + 3 ^ 40 * 5794422 * 2
def baseEnd_5794422 : Nat := 991774533662211176992315

theorem tailTrace_5794422 : CollatzResearch.WordTrace tailWord_5794422 prefixEnd_5794422 991774533662211176992315 := by
  unfold tailWord_5794422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208745788362886083497095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140893288409204118223969013 13208745788362886083497095)
  ·
    refine ⟨19813118682544329125245643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13208745788362886083497095 19813118682544329125245643)
    ·
      refine ⟨29719678023816493687868465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19813118682544329125245643 29719678023816493687868465)
      ·
        refine ⟨22289758517862370265901349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29719678023816493687868465 22289758517862370265901349)
        ·
          refine ⟨4179329722099194424856503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22289758517862370265901349 4179329722099194424856503)
          ·
            refine ⟨6268994583148791637284755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179329722099194424856503 6268994583148791637284755)
            ·
              refine ⟨9403491874723187455927133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268994583148791637284755 9403491874723187455927133)
              ·
                refine ⟨3526309453021195295972675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9403491874723187455927133 3526309453021195295972675)
                ·
                  refine ⟨5289464179531792943959013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526309453021195295972675 5289464179531792943959013)
                  ·
                    refine ⟨991774533662211176992315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289464179531792943959013 991774533662211176992315)
                    ·
                      rfl

theorem cell23_5794422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_5794422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794422 prefixEnd_5794422 := by exact prefixLift 5794422
  have htrace : WordTrace (prefixWord ++ tailWord_5794422) baseStart_5794422 baseEnd_5794422 := by
    simpa [prefixWord, tailWord_5794422, baseEnd_5794422] using wordTrace_append hprefix tailTrace_5794422
  have hstable : (prefixWord ++ tailWord_5794422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794422).length < 2 ^ (prefixWord ++ tailWord_5794422).sum := by decide
  have hdescent : baseEnd_5794422 < baseStart_5794422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794428 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_5794428 : Nat := 118140960795 + 5794428 * 2 ^ 59
def prefixEnd_5794428 : Nat := 4983230072969 + 3 ^ 40 * 5794428 * 2
def baseEnd_5794428 : Nat := 2975326681870560507501917

theorem tailTrace_5794428 : CollatzResearch.WordTrace tailWord_5794428 prefixEnd_5794428 2975326681870560507501917 := by
  unfold tailWord_5794428
  simp only [CollatzResearch.WordTrace]
  refine ⟨105670075725892220180335969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140893434301189626907114625 105670075725892220180335969)
  ·
    refine ⟨79252556794419165135251977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105670075725892220180335969 79252556794419165135251977)
    ·
      refine ⟨59439417595814373851438983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79252556794419165135251977 59439417595814373851438983)
      ·
        refine ⟨89159126393721560777158475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59439417595814373851438983 89159126393721560777158475)
        ·
          refine ⟨133738689590582341165737713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89159126393721560777158475 133738689590582341165737713)
          ·
            refine ⟨100304017192936755874303285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133738689590582341165737713 100304017192936755874303285)
            ·
              refine ⟨9403501611837820863215933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100304017192936755874303285 9403501611837820863215933)
              ·
                refine ⟨3526313104439182823705975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9403501611837820863215933 3526313104439182823705975)
                ·
                  refine ⟨5289469656658774235558963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526313104439182823705975 5289469656658774235558963)
                  ·
                    refine ⟨7934204484988161353338445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5289469656658774235558963 7934204484988161353338445)
                    ·
                      refine ⟨2975326681870560507501917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7934204484988161353338445 2975326681870560507501917)
                      ·
                        rfl

theorem cell23_5794428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_5794428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794428 prefixEnd_5794428 := by exact prefixLift 5794428
  have htrace : WordTrace (prefixWord ++ tailWord_5794428) baseStart_5794428 baseEnd_5794428 := by
    simpa [prefixWord, tailWord_5794428, baseEnd_5794428] using wordTrace_append hprefix tailTrace_5794428
  have hstable : (prefixWord ++ tailWord_5794428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794428).length < 2 ^ (prefixWord ++ tailWord_5794428).sum := by decide
  have hdescent : baseEnd_5794428 < baseStart_5794428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794447 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_5794447 : Nat := 118140960795 + 5794447 * 2 ^ 59
def prefixEnd_5794447 : Nat := 4983230072969 + 3 ^ 40 * 5794447 * 2
def baseEnd_5794447 : Nat := 2975336438002995933164329

theorem tailTrace_5794447 : CollatzResearch.WordTrace tailWord_5794447 prefixEnd_5794447 2975336438002995933164329 := by
  unfold tailWord_5794447
  simp only [CollatzResearch.WordTrace]
  refine ⟨211340844438715606605613595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140893896292477071070409063 211340844438715606605613595)
  ·
    refine ⟨317011266658073409908420393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211340844438715606605613595 317011266658073409908420393)
    ·
      refine ⟨237758449993555057431315295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317011266658073409908420393 237758449993555057431315295)
      ·
        refine ⟨356637674990332586146972943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237758449993555057431315295 356637674990332586146972943)
        ·
          refine ⟨534956512485498879220459415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356637674990332586146972943 534956512485498879220459415)
          ·
            refine ⟨802434768728248318830689123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534956512485498879220459415 802434768728248318830689123)
            ·
              refine ⟨1203652153092372478246033685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802434768728248318830689123 1203652153092372478246033685)
              ·
                refine ⟨56421194676204959917782829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1203652153092372478246033685 56421194676204959917782829)
                ·
                  refine ⟨21157948003576859969168561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56421194676204959917782829 21157948003576859969168561)
                  ·
                    refine ⟨15868461002682644976876421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21157948003576859969168561 15868461002682644976876421)
                    ·
                      refine ⟨2975336438002995933164329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15868461002682644976876421 2975336438002995933164329)
                      ·
                        rfl

theorem cell23_5794447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_5794447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794447 prefixEnd_5794447 := by exact prefixLift 5794447
  have htrace : WordTrace (prefixWord ++ tailWord_5794447) baseStart_5794447 baseEnd_5794447 := by
    simpa [prefixWord, tailWord_5794447, baseEnd_5794447] using wordTrace_append hprefix tailTrace_5794447
  have hstable : (prefixWord ++ tailWord_5794447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794447).length < 2 ^ (prefixWord ++ tailWord_5794447).sum := by decide
  have hdescent : baseEnd_5794447 < baseStart_5794447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794457 : List Nat := [1, 2, 1, 2, 1, 2, 6, 8]
def baseStart_5794457 : Nat := 118140960795 + 5794457 * 2 ^ 59
def prefixEnd_5794457 : Nat := 4983230072969 + 3 ^ 40 * 5794457 * 2
def baseEnd_5794457 : Nat := 110197836029982996075529

theorem tailTrace_5794457 : CollatzResearch.WordTrace tailWord_5794457 prefixEnd_5794457 110197836029982996075529 := by
  unfold tailWord_5794457
  simp only [CollatzResearch.WordTrace]
  refine ⟨211341209168679378313477625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140894139445786252208985083 211341209168679378313477625)
  ·
    refine ⟨158505906876509533735108219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211341209168679378313477625 158505906876509533735108219)
    ·
      refine ⟨237758860314764300602662329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158505906876509533735108219 237758860314764300602662329)
      ·
        refine ⟨178319145236073225451996747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237758860314764300602662329 178319145236073225451996747)
        ·
          refine ⟨267478717854109838177995121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178319145236073225451996747 267478717854109838177995121)
          ·
            refine ⟨200609038390582378633496341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267478717854109838177995121 200609038390582378633496341)
            ·
              refine ⟨9403548674558548998445141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200609038390582378633496341 9403548674558548998445141)
              ·
                refine ⟨110197836029982996075529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9403548674558548998445141 110197836029982996075529)
                ·
                  rfl

theorem cell23_5794457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 8].length) (baseStart_5794457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794457 prefixEnd_5794457 := by exact prefixLift 5794457
  have htrace : WordTrace (prefixWord ++ tailWord_5794457) baseStart_5794457 baseEnd_5794457 := by
    simpa [prefixWord, tailWord_5794457, baseEnd_5794457] using wordTrace_append hprefix tailTrace_5794457
  have hstable : (prefixWord ++ tailWord_5794457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794457).length < 2 ^ (prefixWord ++ tailWord_5794457).sum := by decide
  have hdescent : baseEnd_5794457 < baseStart_5794457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794547 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 11]
def baseStart_5794547 : Nat := 118140960795 + 5794547 * 2 ^ 59
def prefixEnd_5794547 : Nat := 4983230072969 + 3 ^ 40 * 5794547 * 2
def baseEnd_5794547 : Nat := 330598642896493949101541

theorem tailTrace_5794547 : CollatzResearch.WordTrace tailWord_5794547 prefixEnd_5794547 330598642896493949101541 := by
  unfold tailWord_5794547
  simp only [CollatzResearch.WordTrace]
  refine ⟨211344491738353323684253895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140896327825568882456169263 211344491738353323684253895)
  ·
    refine ⟨317016737607529985526380843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211344491738353323684253895 317016737607529985526380843)
    ·
      refine ⟨475525106411294978289571265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317016737607529985526380843 475525106411294978289571265)
      ·
        refine ⟨356643829808471233717178449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475525106411294978289571265 356643829808471233717178449)
        ·
          refine ⟨267482872356353425287883837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356643829808471233717178449 267482872356353425287883837)
          ·
            refine ⟨100306077133632534482956439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267482872356353425287883837 100306077133632534482956439)
            ·
              refine ⟨150459115700448801724434659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100306077133632534482956439 150459115700448801724434659)
              ·
                refine ⟨225688673550673202586651989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150459115700448801724434659 225688673550673202586651989)
                ·
                  refine ⟨330598642896493949101541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 225688673550673202586651989 330598642896493949101541)
                  ·
                    rfl

theorem cell23_5794547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 11].length) (baseStart_5794547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794547 prefixEnd_5794547 := by exact prefixLift 5794547
  have htrace : WordTrace (prefixWord ++ tailWord_5794547) baseStart_5794547 baseEnd_5794547 := by
    simpa [prefixWord, tailWord_5794547, baseEnd_5794547] using wordTrace_append hprefix tailTrace_5794547
  have hstable : (prefixWord ++ tailWord_5794547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794547).length < 2 ^ (prefixWord ++ tailWord_5794547).sum := by decide
  have hdescent : baseEnd_5794547 < baseStart_5794547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794554 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_5794554 : Nat := 118140960795 + 5794554 * 2 ^ 59
def prefixEnd_5794554 : Nat := 4983230072969 + 3 ^ 40 * 5794554 * 2
def baseEnd_5794554 : Nat := 2975391380433027014526337

theorem tailTrace_5794554 : CollatzResearch.WordTrace tailWord_5794554 prefixEnd_5794554 2975391380433027014526337 := by
  unfold tailWord_5794554
  simp only [CollatzResearch.WordTrace]
  refine ⟨52836186762331990969939679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140896498032885309253172477 52836186762331990969939679)
  ·
    refine ⟨79254280143497986454909519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52836186762331990969939679 79254280143497986454909519)
    ·
      refine ⟨118881420215246979682364279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79254280143497986454909519 118881420215246979682364279)
      ·
        refine ⟨178322130322870469523546419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118881420215246979682364279 178322130322870469523546419)
        ·
          refine ⟨267483195484305704285319629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178322130322870469523546419 267483195484305704285319629)
          ·
            refine ⟨100306198306614639106994861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267483195484305704285319629 100306198306614639106994861)
            ·
              refine ⟨37614824364980489665123073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100306198306614639106994861 37614824364980489665123073)
              ·
                refine ⟨28211118273735367248842305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37614824364980489665123073 28211118273735367248842305)
                ·
                  refine ⟨21158338705301525436631729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28211118273735367248842305 21158338705301525436631729)
                  ·
                    refine ⟨15868754028976144077473797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21158338705301525436631729 15868754028976144077473797)
                    ·
                      refine ⟨2975391380433027014526337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15868754028976144077473797 2975391380433027014526337)
                      ·
                        rfl

theorem cell23_5794554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_5794554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794554 prefixEnd_5794554 := by exact prefixLift 5794554
  have htrace : WordTrace (prefixWord ++ tailWord_5794554) baseStart_5794554 baseEnd_5794554 := by
    simpa [prefixWord, tailWord_5794554, baseEnd_5794554] using wordTrace_append hprefix tailTrace_5794554
  have hstable : (prefixWord ++ tailWord_5794554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794554).length < 2 ^ (prefixWord ++ tailWord_5794554).sum := by decide
  have hdescent : baseEnd_5794554 < baseStart_5794554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794575 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 2, 2, 2]
def baseStart_5794575 : Nat := 118140960795 + 5794575 * 2 ^ 59
def prefixEnd_5794575 : Nat := 4983230072969 + 3 ^ 40 * 5794575 * 2
def baseEnd_5794575 : Nat := 2975402163526771432363741

theorem tailTrace_5794575 : CollatzResearch.WordTrace tailWord_5794575 prefixEnd_5794575 2975402163526771432363741 := by
  unfold tailWord_5794575
  simp only [CollatzResearch.WordTrace]
  refine ⟨211345512982251884466273179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140897008654834589644182119 211345512982251884466273179)
  ·
    refine ⟨317018269473377826699409769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211345512982251884466273179 317018269473377826699409769)
    ·
      refine ⟨237763702105033370024557327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317018269473377826699409769 237763702105033370024557327)
      ·
        refine ⟨356645553157550055036835991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237763702105033370024557327 356645553157550055036835991)
        ·
          refine ⟨534968329736325082555253987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356645553157550055036835991 534968329736325082555253987)
          ·
            refine ⟨802452494604487623832880981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534968329736325082555253987 802452494604487623832880981)
            ·
              refine ⟨4701870085573169670895787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 802452494604487623832880981 4701870085573169670895787)
              ·
                refine ⟨7052805128359754506343681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701870085573169670895787 7052805128359754506343681)
                ·
                  refine ⟨5289603846269815879757761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052805128359754506343681 5289603846269815879757761)
                  ·
                    refine ⟨3967202884702361909818321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5289603846269815879757761 3967202884702361909818321)
                    ·
                      refine ⟨2975402163526771432363741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967202884702361909818321 2975402163526771432363741)
                      ·
                        rfl

theorem cell23_5794575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 2, 2].length) (baseStart_5794575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794575 prefixEnd_5794575 := by exact prefixLift 5794575
  have htrace : WordTrace (prefixWord ++ tailWord_5794575) baseStart_5794575 baseEnd_5794575 := by
    simpa [prefixWord, tailWord_5794575, baseEnd_5794575] using wordTrace_append hprefix tailTrace_5794575
  have hstable : (prefixWord ++ tailWord_5794575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794575).length < 2 ^ (prefixWord ++ tailWord_5794575).sum := by decide
  have hdescent : baseEnd_5794575 < baseStart_5794575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794604 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_5794604 : Nat := 118140960795 + 5794604 * 2 ^ 59
def prefixEnd_5794604 : Nat := 4983230072969 + 3 ^ 40 * 5794604 * 2
def baseEnd_5794604 : Nat := 2975417054465751818901107

theorem tailTrace_5794604 : CollatzResearch.WordTrace tailWord_5794604 prefixEnd_5794604 2975417054465751818901107 := by
  unfold tailWord_5794604
  simp only [CollatzResearch.WordTrace]
  refine ⟨105673285349573411209539433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140897713799431214946052577 105673285349573411209539433)
  ·
    refine ⟨79254964012180058407154575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105673285349573411209539433 79254964012180058407154575)
    ·
      refine ⟨118882446018270087610731863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79254964012180058407154575 118882446018270087610731863)
      ·
        refine ⟨178323669027405131416097795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118882446018270087610731863 178323669027405131416097795)
        ·
          refine ⟨267485503541107697124146693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178323669027405131416097795 267485503541107697124146693)
          ·
            refine ⟨50153531913957693210777505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267485503541107697124146693 50153531913957693210777505)
            ·
              refine ⟨37615148935468269908083129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50153531913957693210777505 37615148935468269908083129)
              ·
                refine ⟨28211361701601202431062347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37615148935468269908083129 28211361701601202431062347)
                ·
                  refine ⟨42317042552401803646593521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28211361701601202431062347 42317042552401803646593521)
                  ·
                    refine ⟨31737781914301352734945141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42317042552401803646593521 31737781914301352734945141)
                    ·
                      refine ⟨2975417054465751818901107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31737781914301352734945141 2975417054465751818901107)
                      ·
                        rfl

theorem cell23_5794604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_5794604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794604 prefixEnd_5794604 := by exact prefixLift 5794604
  have htrace : WordTrace (prefixWord ++ tailWord_5794604) baseStart_5794604 baseEnd_5794604 := by
    simpa [prefixWord, tailWord_5794604, baseEnd_5794604] using wordTrace_append hprefix tailTrace_5794604
  have hstable : (prefixWord ++ tailWord_5794604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794604).length < 2 ^ (prefixWord ++ tailWord_5794604).sum := by decide
  have hdescent : baseEnd_5794604 < baseStart_5794604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794611 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 2, 5]
def baseStart_5794611 : Nat := 118140960795 + 5794611 * 2 ^ 59
def prefixEnd_5794611 : Nat := 4983230072969 + 3 ^ 40 * 5794611 * 2
def baseEnd_5794611 : Nat := 991806882943444430504525

theorem tailTrace_5794611 : CollatzResearch.WordTrace tailWord_5794611 prefixEnd_5794611 991806882943444430504525 := by
  unfold tailWord_5794611
  simp only [CollatzResearch.WordTrace]
  refine ⟨211346826010121462614583687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140897884006747641743055791 211346826010121462614583687)
  ·
    refine ⟨317020239015182193921875531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211346826010121462614583687 317020239015182193921875531)
    ·
      refine ⟨475530358522773290882813297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317020239015182193921875531 475530358522773290882813297)
      ·
        refine ⟨356647768892079968162109973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475530358522773290882813297 356647768892079968162109973)
        ·
          refine ⟨16717864166816248507598905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 356647768892079968162109973 16717864166816248507598905)
          ·
            refine ⟨12538398125112186380699179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16717864166816248507598905 12538398125112186380699179)
            ·
              refine ⟨18807597187668279571048769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12538398125112186380699179 18807597187668279571048769)
              ·
                refine ⟨14105697890751209678286577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18807597187668279571048769 14105697890751209678286577)
                ·
                  refine ⟨10579273418063407258714933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14105697890751209678286577 10579273418063407258714933)
                  ·
                    refine ⟨991806882943444430504525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10579273418063407258714933 991806882943444430504525)
                    ·
                      rfl

theorem cell23_5794611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 5].length) (baseStart_5794611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794611 prefixEnd_5794611 := by exact prefixLift 5794611
  have htrace : WordTrace (prefixWord ++ tailWord_5794611) baseStart_5794611 baseEnd_5794611 := by
    simpa [prefixWord, tailWord_5794611, baseEnd_5794611] using wordTrace_append hprefix tailTrace_5794611
  have hstable : (prefixWord ++ tailWord_5794611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794611).length < 2 ^ (prefixWord ++ tailWord_5794611).sum := by decide
  have hdescent : baseEnd_5794611 < baseStart_5794611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794631 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_5794631 : Nat := 118140960795 + 5794631 * 2 ^ 59
def prefixEnd_5794631 : Nat := 4983230072969 + 3 ^ 40 * 5794631 * 2
def baseEnd_5794631 : Nat := 2975430918443423213263483

theorem tailTrace_5794631 : CollatzResearch.WordTrace tailWord_5794631 prefixEnd_5794631 2975430918443423213263483 := by
  unfold tailWord_5794631
  simp only [CollatzResearch.WordTrace]
  refine ⟨211347555470049006030311747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140898370313366004020207831 211347555470049006030311747)
  ·
    refine ⟨317021333205073509045467621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211347555470049006030311747 317021333205073509045467621)
    ·
      refine ⟨59441499975951282946025179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317021333205073509045467621 59441499975951282946025179)
      ·
        refine ⟨89162249963926924419037769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59441499975951282946025179 89162249963926924419037769)
        ·
          refine ⟨66871687472945193314278327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89162249963926924419037769 66871687472945193314278327)
          ·
            refine ⟨100307531209417789971417491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66871687472945193314278327 100307531209417789971417491)
            ·
              refine ⟨150461296814126684957126237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100307531209417789971417491 150461296814126684957126237)
              ·
                refine ⟨56422986305297506858922339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150461296814126684957126237 56422986305297506858922339)
                ·
                  refine ⟨84634479457946260288383509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56422986305297506858922339 84634479457946260288383509)
                  ·
                    refine ⟨3967241224591230951017977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84634479457946260288383509 3967241224591230951017977)
                    ·
                      refine ⟨2975430918443423213263483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967241224591230951017977 2975430918443423213263483)
                      ·
                        rfl

theorem cell23_5794631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_5794631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794631 prefixEnd_5794631 := by exact prefixLift 5794631
  have htrace : WordTrace (prefixWord ++ tailWord_5794631) baseStart_5794631 baseEnd_5794631 := by
    simpa [prefixWord, tailWord_5794631, baseEnd_5794631] using wordTrace_append hprefix tailTrace_5794631
  have hstable : (prefixWord ++ tailWord_5794631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794631).length < 2 ^ (prefixWord ++ tailWord_5794631).sum := by decide
  have hdescent : baseEnd_5794631 < baseStart_5794631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794675 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 1, 4]
def baseStart_5794675 : Nat := 118140960795 + 5794675 * 2 ^ 59
def prefixEnd_5794675 : Nat := 4983230072969 + 3 ^ 40 * 5794675 * 2
def baseEnd_5794675 : Nat := 991817837197407013704427

theorem tailTrace_5794675 : CollatzResearch.WordTrace tailWord_5794675 prefixEnd_5794675 991817837197407013704427 := by
  unfold tailWord_5794675
  simp only [CollatzResearch.WordTrace]
  refine ⟨211349160281889601544913479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140899440187926401029942319 211349160281889601544913479)
  ·
    refine ⟨317023740422834402317370219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211349160281889601544913479 317023740422834402317370219)
    ·
      refine ⟨475535610634251603476055329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317023740422834402317370219 475535610634251603476055329)
      ·
        refine ⟨356651707975688702607041497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475535610634251603476055329 356651707975688702607041497)
        ·
          refine ⟨267488780981766526955281123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356651707975688702607041497 267488780981766526955281123)
          ·
            refine ⟨401233171472649790432921685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267488780981766526955281123 401233171472649790432921685)
            ·
              refine ⟨4701951228195114731635801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 401233171472649790432921685 4701951228195114731635801)
              ·
                refine ⟨3526463421146336048726851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4701951228195114731635801 3526463421146336048726851)
                ·
                  refine ⟨5289695131719504073090277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526463421146336048726851 5289695131719504073090277)
                  ·
                    refine ⟨991817837197407013704427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289695131719504073090277 991817837197407013704427)
                    ·
                      rfl

theorem cell23_5794675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 4].length) (baseStart_5794675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794675 prefixEnd_5794675 := by exact prefixLift 5794675
  have htrace : WordTrace (prefixWord ++ tailWord_5794675) baseStart_5794675 baseEnd_5794675 := by
    simpa [prefixWord, tailWord_5794675, baseEnd_5794675] using wordTrace_append hprefix tailTrace_5794675
  have hstable : (prefixWord ++ tailWord_5794675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794675).length < 2 ^ (prefixWord ++ tailWord_5794675).sum := by decide
  have hdescent : baseEnd_5794675 < baseStart_5794675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794731 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 4, 4]
def baseStart_5794731 : Nat := 118140960795 + 5794731 * 2 ^ 59
def prefixEnd_5794731 : Nat := 4983230072969 + 3 ^ 40 * 5794731 * 2
def baseEnd_5794731 : Nat := 991827422169624274004341

theorem tailTrace_5794731 : CollatzResearch.WordTrace tailWord_5794731 prefixEnd_5794731 991827422169624274004341 := by
  unfold tailWord_5794731
  simp only [CollatzResearch.WordTrace]
  refine ⟨211351202769686723108952047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140900801846457815405968031 211351202769686723108952047)
  ·
    refine ⟨317026804154530084663428071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211351202769686723108952047 317026804154530084663428071)
    ·
      refine ⟨475540206231795126995142107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317026804154530084663428071 475540206231795126995142107)
      ·
        refine ⟨713310309347692690492713161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475540206231795126995142107 713310309347692690492713161)
        ·
          refine ⟨534982732010769517869534871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713310309347692690492713161 534982732010769517869534871)
          ·
            refine ⟨802474098016154276804302307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534982732010769517869534871 802474098016154276804302307)
            ·
              refine ⟨1203711147024231415206453461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802474098016154276804302307 1203711147024231415206453461)
              ·
                refine ⟨28211980008380423793901253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1203711147024231415206453461 28211980008380423793901253)
                ·
                  refine ⟨5289746251571329461356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28211980008380423793901253 5289746251571329461356485)
                  ·
                    refine ⟨991827422169624274004341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289746251571329461356485 991827422169624274004341)
                    ·
                      rfl

theorem cell23_5794731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 4].length) (baseStart_5794731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794731 prefixEnd_5794731 := by exact prefixLift 5794731
  have htrace : WordTrace (prefixWord ++ tailWord_5794731) baseStart_5794731 baseEnd_5794731 := by
    simpa [prefixWord, tailWord_5794731, baseEnd_5794731] using wordTrace_append hprefix tailTrace_5794731
  have hstable : (prefixWord ++ tailWord_5794731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794731).length < 2 ^ (prefixWord ++ tailWord_5794731).sum := by decide
  have hdescent : baseEnd_5794731 < baseStart_5794731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794751 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_5794751 : Nat := 118140960795 + 5794751 * 2 ^ 59
def prefixEnd_5794751 : Nat := 4983230072969 + 3 ^ 40 * 5794751 * 2
def baseEnd_5794751 : Nat := 2975492536121962743762931

theorem tailTrace_5794751 : CollatzResearch.WordTrace tailWord_5794751 prefixEnd_5794751 2975492536121962743762931 := by
  unfold tailWord_5794751
  simp only [CollatzResearch.WordTrace]
  refine ⟨211351932229614266524680107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140901288153076177683120071 211351932229614266524680107)
  ·
    refine ⟨317027898344421399787020161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211351932229614266524680107 317027898344421399787020161)
    ·
      refine ⟨237770923758316049840265121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317027898344421399787020161 237770923758316049840265121)
      ·
        refine ⟨178328192818737037380198841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237770923758316049840265121 178328192818737037380198841)
        ·
          refine ⟨133746144614052778035149131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178328192818737037380198841 133746144614052778035149131)
          ·
            refine ⟨200619216921079167052723697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133746144614052778035149131 200619216921079167052723697)
            ·
              refine ⟨150464412690809375289542773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200619216921079167052723697 150464412690809375289542773)
              ·
                refine ⟨14106038689763378933394635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150464412690809375289542773 14106038689763378933394635)
                ·
                  refine ⟨21159058034645068400091953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14106038689763378933394635 21159058034645068400091953)
                  ·
                    refine ⟨15869293525983801300068965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21159058034645068400091953 15869293525983801300068965)
                    ·
                      refine ⟨2975492536121962743762931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15869293525983801300068965 2975492536121962743762931)
                      ·
                        rfl

theorem cell23_5794751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_5794751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794751 prefixEnd_5794751 := by exact prefixLift 5794751
  have htrace : WordTrace (prefixWord ++ tailWord_5794751) baseStart_5794751 baseEnd_5794751 := by
    simpa [prefixWord, tailWord_5794751, baseEnd_5794751] using wordTrace_append hprefix tailTrace_5794751
  have hstable : (prefixWord ++ tailWord_5794751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794751).length < 2 ^ (prefixWord ++ tailWord_5794751).sum := by decide
  have hdescent : baseEnd_5794751 < baseStart_5794751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794855 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5794855 : Nat := 118140960795 + 5794855 * 2 ^ 59
def prefixEnd_5794855 : Nat := 4983230072969 + 3 ^ 40 * 5794855 * 2
def baseEnd_5794855 : Nat := 991848646036676778954151

theorem tailTrace_5794855 : CollatzResearch.WordTrace tailWord_5794855 prefixEnd_5794855 991848646036676778954151 := by
  unfold tailWord_5794855
  simp only [CollatzResearch.WordTrace]
  refine ⟨211355725421237492286466019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140903816947491661524310679 211355725421237492286466019)
  ·
    refine ⟨317033588131856238429699029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211355725421237492286466019 317033588131856238429699029)
    ·
      refine ⟨7430474721840380588196071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 317033588131856238429699029 7430474721840380588196071)
      ·
        refine ⟨11145712082760570882294107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430474721840380588196071 11145712082760570882294107)
        ·
          refine ⟨16718568124140856323441161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11145712082760570882294107 16718568124140856323441161)
          ·
            refine ⟨12538926093105642242580871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16718568124140856323441161 12538926093105642242580871)
            ·
              refine ⟨18808389139658463363871307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12538926093105642242580871 18808389139658463363871307)
              ·
                refine ⟨28212583709487695045806961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18808389139658463363871307 28212583709487695045806961)
                ·
                  refine ⟨21159437782115771284355221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28212583709487695045806961 21159437782115771284355221)
                  ·
                    refine ⟨991848646036676778954151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21159437782115771284355221 991848646036676778954151)
                    ·
                      rfl

theorem cell23_5794855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5794855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794855 prefixEnd_5794855 := by exact prefixLift 5794855
  have htrace : WordTrace (prefixWord ++ tailWord_5794855) baseStart_5794855 baseEnd_5794855 := by
    simpa [prefixWord, tailWord_5794855, baseEnd_5794855] using wordTrace_append hprefix tailTrace_5794855
  have hstable : (prefixWord ++ tailWord_5794855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794855).length < 2 ^ (prefixWord ++ tailWord_5794855).sum := by decide
  have hdescent : baseEnd_5794855 < baseStart_5794855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794862 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5794862 : Nat := 118140960795 + 5794862 * 2 ^ 59
def prefixEnd_5794862 : Nat := 4983230072969 + 3 ^ 40 * 5794862 * 2
def baseEnd_5794862 : Nat := 2975549532474611809474921

theorem tailTrace_5794862 : CollatzResearch.WordTrace tailWord_5794862 prefixEnd_5794862 2975549532474611809474921 := by
  unfold tailWord_5794862
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419497591526516560246355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140903987154808088321313893 26419497591526516560246355)
  ·
    refine ⟨39629246387289774840369533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26419497591526516560246355 39629246387289774840369533)
    ·
      refine ⟨14860967395233665565138575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39629246387289774840369533 14860967395233665565138575)
      ·
        refine ⟨22291451092850498347707863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14860967395233665565138575 22291451092850498347707863)
        ·
          refine ⟨33437176639275747521561795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22291451092850498347707863 33437176639275747521561795)
          ·
            refine ⟨50155764958913621282342693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33437176639275747521561795 50155764958913621282342693)
            ·
              refine ⟨9404205929796303990439255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50155764958913621282342693 9404205929796303990439255)
              ·
                refine ⟨14106308894694455985658883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9404205929796303990439255 14106308894694455985658883)
                ·
                  refine ⟨21159463342041683978488325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14106308894694455985658883 21159463342041683978488325)
                  ·
                    refine ⟨3967399376632815745966561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21159463342041683978488325 3967399376632815745966561)
                    ·
                      refine ⟨2975549532474611809474921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967399376632815745966561 2975549532474611809474921)
                      ·
                        rfl

theorem cell23_5794862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5794862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794862 prefixEnd_5794862 := by exact prefixLift 5794862
  have htrace : WordTrace (prefixWord ++ tailWord_5794862) baseStart_5794862 baseEnd_5794862 := by
    simpa [prefixWord, tailWord_5794862, baseEnd_5794862] using wordTrace_append hprefix tailTrace_5794862
  have hstable : (prefixWord ++ tailWord_5794862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794862).length < 2 ^ (prefixWord ++ tailWord_5794862).sum := by decide
  have hdescent : baseEnd_5794862 < baseStart_5794862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794908 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5794908 : Nat := 118140960795 + 5794908 * 2 ^ 59
def prefixEnd_5794908 : Nat := 4983230072969 + 3 ^ 40 * 5794908 * 2
def baseEnd_5794908 : Nat := 2975573152584718629499709

theorem tailTrace_5794908 : CollatzResearch.WordTrace tailWord_5794908 prefixEnd_5794908 2975573152584718629499709 := by
  unfold tailWord_5794908
  simp only [CollatzResearch.WordTrace]
  refine ⟨105678829245022741169072689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140905105660030321558763585 105678829245022741169072689)
  ·
    refine ⟨79259121933767055876804517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105678829245022741169072689 79259121933767055876804517)
    ·
      refine ⟨14861085362581322976900847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79259121933767055876804517 14861085362581322976900847)
      ·
        refine ⟨22291628043871984465351271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14861085362581322976900847 22291628043871984465351271)
        ·
          refine ⟨33437442065807976698026907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22291628043871984465351271 33437442065807976698026907)
          ·
            refine ⟨50156163098711965047040361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33437442065807976698026907 50156163098711965047040361)
            ·
              refine ⟨37617122324033973785280271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50156163098711965047040361 37617122324033973785280271)
              ·
                refine ⟨56425683486050960677920407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37617122324033973785280271 56425683486050960677920407)
                ·
                  refine ⟨84638525229076441016880611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56425683486050960677920407 84638525229076441016880611)
                  ·
                    refine ⟨126957787843614661525320917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84638525229076441016880611 126957787843614661525320917)
                    ·
                      refine ⟨2975573152584718629499709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126957787843614661525320917 2975573152584718629499709)
                      ·
                        rfl

theorem cell23_5794908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5794908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794908 prefixEnd_5794908 := by exact prefixLift 5794908
  have htrace : WordTrace (prefixWord ++ tailWord_5794908) baseStart_5794908 baseEnd_5794908 := by
    simpa [prefixWord, tailWord_5794908, baseEnd_5794908] using wordTrace_append hprefix tailTrace_5794908
  have hstable : (prefixWord ++ tailWord_5794908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794908).length < 2 ^ (prefixWord ++ tailWord_5794908).sum := by decide
  have hdescent : baseEnd_5794908 < baseStart_5794908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794952 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5794952 : Nat := 118140960795 + 5794952 * 2 ^ 59
def prefixEnd_5794952 : Nat := 4983230072969 + 3 ^ 40 * 5794952 * 2
def baseEnd_5794952 : Nat := 2975595745733516457349507

theorem tailTrace_5794952 : CollatzResearch.WordTrace tailWord_5794952 prefixEnd_5794952 2975595745733516457349507 := by
  unfold tailWord_5794952
  simp only [CollatzResearch.WordTrace]
  refine ⟨105679631650943038926373555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140906175534590718568498073 105679631650943038926373555)
  ·
    refine ⟨158519447476414558389560333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105679631650943038926373555 158519447476414558389560333)
    ·
      refine ⟨59444792803655459396085125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158519447476414558389560333 59444792803655459396085125)
      ·
        refine ⟨11145898650685398636765961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59444792803655459396085125 11145898650685398636765961)
        ·
          refine ⟨8359423988014048977574471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11145898650685398636765961 8359423988014048977574471)
          ·
            refine ⟨12539135982021073466361707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359423988014048977574471 12539135982021073466361707)
            ·
              refine ⟨18808703973031610199542561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12539135982021073466361707 18808703973031610199542561)
              ·
                refine ⟨14106527979773707649656921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18808703973031610199542561 14106527979773707649656921)
                ·
                  refine ⟨10579895984830280737242691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14106527979773707649656921 10579895984830280737242691)
                  ·
                    refine ⟨15869843977245421105864037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10579895984830280737242691 15869843977245421105864037)
                    ·
                      refine ⟨2975595745733516457349507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15869843977245421105864037 2975595745733516457349507)
                      ·
                        rfl

theorem cell23_5794952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5794952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794952 prefixEnd_5794952 := by exact prefixLift 5794952
  have htrace : WordTrace (prefixWord ++ tailWord_5794952) baseStart_5794952 baseEnd_5794952 := by
    simpa [prefixWord, tailWord_5794952, baseEnd_5794952] using wordTrace_append hprefix tailTrace_5794952
  have hstable : (prefixWord ++ tailWord_5794952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794952).length < 2 ^ (prefixWord ++ tailWord_5794952).sum := by decide
  have hdescent : baseEnd_5794952 < baseStart_5794952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794962 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_5794962 : Nat := 118140960795 + 5794962 * 2 ^ 59
def prefixEnd_5794962 : Nat := 4983230072969 + 3 ^ 40 * 5794962 * 2
def baseEnd_5794962 : Nat := 991866960180020472741487

theorem tailTrace_5794962 : CollatzResearch.WordTrace tailWord_5794962 prefixEnd_5794962 991866960180020472741487 := by
  unfold tailWord_5794962
  simp only [CollatzResearch.WordTrace]
  refine ⟨52839907007962462390152785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140906418687899899707074093 52839907007962462390152785)
  ·
    refine ⟨39629930255971846792614589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52839907007962462390152785 39629930255971846792614589)
    ·
      refine ⟨14861223845989442547230471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39629930255971846792614589 14861223845989442547230471)
      ·
        refine ⟨22291835768984163820845707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14861223845989442547230471 22291835768984163820845707)
        ·
          refine ⟨33437753653476245731268561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22291835768984163820845707 33437753653476245731268561)
          ·
            refine ⟨25078315240107184298451421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33437753653476245731268561 25078315240107184298451421)
            ·
              refine ⟨9404368215040194111919283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25078315240107184298451421 9404368215040194111919283)
              ·
                refine ⟨14106552322560291167878925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9404368215040194111919283 14106552322560291167878925)
                ·
                  refine ⟨5289957120960109187954597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14106552322560291167878925 5289957120960109187954597)
                  ·
                    refine ⟨991866960180020472741487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5289957120960109187954597 991866960180020472741487)
                    ·
                      rfl

theorem cell23_5794962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_5794962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794962 prefixEnd_5794962 := by exact prefixLift 5794962
  have htrace : WordTrace (prefixWord ++ tailWord_5794962) baseStart_5794962 baseEnd_5794962 := by
    simpa [prefixWord, tailWord_5794962, baseEnd_5794962] using wordTrace_append hprefix tailTrace_5794962
  have hstable : (prefixWord ++ tailWord_5794962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794962).length < 2 ^ (prefixWord ++ tailWord_5794962).sum := by decide
  have hdescent : baseEnd_5794962 < baseStart_5794962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794989 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_5794989 : Nat := 118140960795 + 5794989 * 2 ^ 59
def prefixEnd_5794989 : Nat := 4983230072969 + 3 ^ 40 * 5794989 * 2
def baseEnd_5794989 : Nat := 2975614744517732812586837

theorem tailTrace_5794989 : CollatzResearch.WordTrace tailWord_5794989 prefixEnd_5794989 2975614744517732812586837 := by
  unfold tailWord_5794989
  simp only [CollatzResearch.WordTrace]
  refine ⟨211360612802752033171844021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140907075201834688781229347 211360612802752033171844021)
  ·
    refine ⟨19815057450258003109860377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211360612802752033171844021 19815057450258003109860377)
    ·
      refine ⟨14861293087693502332395283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19815057450258003109860377 14861293087693502332395283)
      ·
        refine ⟨22291939631540253498592925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14861293087693502332395283 22291939631540253498592925)
        ·
          refine ⟨8359477361827595061972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22291939631540253498592925 8359477361827595061972347)
          ·
            refine ⟨12539216042741392592958521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359477361827595061972347 12539216042741392592958521)
            ·
              refine ⟨9404412032056044444718891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12539216042741392592958521 9404412032056044444718891)
              ·
                refine ⟨14106618048084066667078337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9404412032056044444718891 14106618048084066667078337)
                ·
                  refine ⟨10579963536063050000308753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14106618048084066667078337 10579963536063050000308753)
                  ·
                    refine ⟨7934972652047287500231565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10579963536063050000308753 7934972652047287500231565)
                    ·
                      refine ⟨2975614744517732812586837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7934972652047287500231565 2975614744517732812586837)
                      ·
                        rfl

theorem cell23_5794989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_5794989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794989 prefixEnd_5794989 := by exact prefixLift 5794989
  have htrace : WordTrace (prefixWord ++ tailWord_5794989) baseStart_5794989 baseEnd_5794989 := by
    simpa [prefixWord, tailWord_5794989, baseEnd_5794989] using wordTrace_append hprefix tailTrace_5794989
  have hstable : (prefixWord ++ tailWord_5794989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794989).length < 2 ^ (prefixWord ++ tailWord_5794989).sum := by decide
  have hdescent : baseEnd_5794989 < baseStart_5794989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5794995 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 5, 2]
def baseStart_5794995 : Nat := 118140960795 + 5794995 * 2 ^ 59
def prefixEnd_5794995 : Nat := 4983230072969 + 3 ^ 40 * 5794995 * 2
def baseEnd_5794995 : Nat := 2975617825401659789111809

theorem tailTrace_5794995 : CollatzResearch.WordTrace tailWord_5794995 prefixEnd_5794995 2975617825401659789111809 := by
  unfold tailWord_5794995
  simp only [CollatzResearch.WordTrace]
  refine ⟨211360831640730296196562439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140907221093820197464374959 211360831640730296196562439)
  ·
    refine ⟨317041247461095444294843659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211360831640730296196562439 317041247461095444294843659)
    ·
      refine ⟨475561871191643166442265489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317041247461095444294843659 475561871191643166442265489)
      ·
        refine ⟨356671403393732374831699117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475561871191643166442265489 356671403393732374831699117)
        ·
          refine ⟨133751776272649640561887169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356671403393732374831699117 133751776272649640561887169)
          ·
            refine ⟨100313832204487230421415377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133751776272649640561887169 100313832204487230421415377)
            ·
              refine ⟨75235374153365422816061533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100313832204487230421415377 75235374153365422816061533)
              ·
                refine ⟨28213265307512033556023075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75235374153365422816061533 28213265307512033556023075)
                ·
                  refine ⟨42319897961268050334034613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28213265307512033556023075 42319897961268050334034613)
                  ·
                    refine ⟨3967490433868879718815745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42319897961268050334034613 3967490433868879718815745)
                    ·
                      refine ⟨2975617825401659789111809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967490433868879718815745 2975617825401659789111809)
                      ·
                        rfl

theorem cell23_5794995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5, 2].length) (baseStart_5794995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5794995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5794995 prefixEnd_5794995 := by exact prefixLift 5794995
  have htrace : WordTrace (prefixWord ++ tailWord_5794995) baseStart_5794995 baseEnd_5794995 := by
    simpa [prefixWord, tailWord_5794995, baseEnd_5794995] using wordTrace_append hprefix tailTrace_5794995
  have hstable : (prefixWord ++ tailWord_5794995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5794995).length < 2 ^ (prefixWord ++ tailWord_5794995).sum := by decide
  have hdescent : baseEnd_5794995 < baseStart_5794995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5794995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795005 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_5795005 : Nat := 118140960795 + 5795005 * 2 ^ 59
def prefixEnd_5795005 : Nat := 4983230072969 + 3 ^ 40 * 5795005 * 2
def baseEnd_5795005 : Nat := 991874320069401583328921

theorem tailTrace_5795005 : CollatzResearch.WordTrace tailWord_5795005 prefixEnd_5795005 991874320069401583328921 := by
  unfold tailWord_5795005
  simp only [CollatzResearch.WordTrace]
  refine ⟨211361196370694067904426469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140907464247129378602950979 211361196370694067904426469)
  ·
    refine ⟨39630224319505137732079963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211361196370694067904426469 39630224319505137732079963)
    ·
      refine ⟨59445336479257706598119945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39630224319505137732079963 59445336479257706598119945)
      ·
        refine ⟨44584002359443279948589959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59445336479257706598119945 44584002359443279948589959)
        ·
          refine ⟨66876003539164919922884939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44584002359443279948589959 66876003539164919922884939)
          ·
            refine ⟨100314005308747379884327409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66876003539164919922884939 100314005308747379884327409)
            ·
              refine ⟨75235503981560534913245557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100314005308747379884327409 75235503981560534913245557)
              ·
                refine ⟨7053328498271300148116771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75235503981560534913245557 7053328498271300148116771)
                ·
                  refine ⟨10579992747406950222175157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7053328498271300148116771 10579992747406950222175157)
                  ·
                    refine ⟨991874320069401583328921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10579992747406950222175157 991874320069401583328921)
                    ·
                      rfl

theorem cell23_5795005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_5795005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795005 prefixEnd_5795005 := by exact prefixLift 5795005
  have htrace : WordTrace (prefixWord ++ tailWord_5795005) baseStart_5795005 baseEnd_5795005 := by
    simpa [prefixWord, tailWord_5795005, baseEnd_5795005] using wordTrace_append hprefix tailTrace_5795005
  have hstable : (prefixWord ++ tailWord_5795005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795005).length < 2 ^ (prefixWord ++ tailWord_5795005).sum := by decide
  have hdescent : baseEnd_5795005 < baseStart_5795005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795025 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_5795025 : Nat := 118140960795 + 5795025 * 2 ^ 59
def prefixEnd_5795025 : Nat := 4983230072969 + 3 ^ 40 * 5795025 * 2
def baseEnd_5795025 : Nat := 2975633229821294671736671

theorem tailTrace_5795025 : CollatzResearch.WordTrace tailWord_5795025 prefixEnd_5795025 2975633229821294671736671 := by
  unfold tailWord_5795025
  simp only [CollatzResearch.WordTrace]
  refine ⟨211361925830621611320154529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140907950553747740880103019 211361925830621611320154529)
  ·
    refine ⟨158521444372966208490115897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211361925830621611320154529 158521444372966208490115897)
    ·
      refine ⟨118891083279724656367586923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158521444372966208490115897 118891083279724656367586923)
      ·
        refine ⟨178336624919586984551380385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118891083279724656367586923 178336624919586984551380385)
        ·
          refine ⟨133752468689690238413535289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178336624919586984551380385 133752468689690238413535289)
          ·
            refine ⟨100314351517267678810151467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133752468689690238413535289 100314351517267678810151467)
            ·
              refine ⟨150471527275901518215227201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100314351517267678810151467 150471527275901518215227201)
              ·
                refine ⟨112853645456926138661420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150471527275901518215227201 112853645456926138661420401)
                ·
                  refine ⟨84640234092694603996065301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112853645456926138661420401 84640234092694603996065301)
                  ·
                    refine ⟨3967510973095059562315561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84640234092694603996065301 3967510973095059562315561)
                    ·
                      refine ⟨2975633229821294671736671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967510973095059562315561 2975633229821294671736671)
                      ·
                        rfl

theorem cell23_5795025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_5795025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795025 prefixEnd_5795025 := by exact prefixLift 5795025
  have htrace : WordTrace (prefixWord ++ tailWord_5795025) baseStart_5795025 baseEnd_5795025 := by
    simpa [prefixWord, tailWord_5795025, baseEnd_5795025] using wordTrace_append hprefix tailTrace_5795025
  have hstable : (prefixWord ++ tailWord_5795025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795025).length < 2 ^ (prefixWord ++ tailWord_5795025).sum := by decide
  have hdescent : baseEnd_5795025 < baseStart_5795025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795059 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 1, 1, 4]
def baseStart_5795059 : Nat := 118140960795 + 5795059 * 2 ^ 59
def prefixEnd_5795059 : Nat := 4983230072969 + 3 ^ 40 * 5795059 * 2
def baseEnd_5795059 : Nat := 2975650688163547538711515

theorem tailTrace_5795059 : CollatzResearch.WordTrace tailWord_5795059 prefixEnd_5795059 2975650688163547538711515 := by
  unfold tailWord_5795059
  simp only [CollatzResearch.WordTrace]
  refine ⟨211363165912498435126892231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140908777274998956751261487 211363165912498435126892231)
  ·
    refine ⟨317044748868747652690338347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211363165912498435126892231 317044748868747652690338347)
    ·
      refine ⟨475567123303121479035507521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317044748868747652690338347 475567123303121479035507521)
      ·
        refine ⟨356675342477341109276630641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475567123303121479035507521 356675342477341109276630641)
        ·
          refine ⟨267506506858005831957472981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356675342477341109276630641 267506506858005831957472981)
          ·
            refine ⟨6269683754484511686503273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 267506506858005831957472981 6269683754484511686503273)
            ·
              refine ⟨4702262815863383764877455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6269683754484511686503273 4702262815863383764877455)
              ·
                refine ⟨7053394223795075647316183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702262815863383764877455 7053394223795075647316183)
                ·
                  refine ⟨10580091335692613470974275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7053394223795075647316183 10580091335692613470974275)
                  ·
                    refine ⟨15870137003538920206461413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10580091335692613470974275 15870137003538920206461413)
                    ·
                      refine ⟨2975650688163547538711515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15870137003538920206461413 2975650688163547538711515)
                      ·
                        rfl

theorem cell23_5795059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 1, 4].length) (baseStart_5795059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795059 prefixEnd_5795059 := by exact prefixLift 5795059
  have htrace : WordTrace (prefixWord ++ tailWord_5795059) baseStart_5795059 baseEnd_5795059 := by
    simpa [prefixWord, tailWord_5795059, baseEnd_5795059] using wordTrace_append hprefix tailTrace_5795059
  have hstable : (prefixWord ++ tailWord_5795059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795059).length < 2 ^ (prefixWord ++ tailWord_5795059).sum := by decide
  have hdescent : baseEnd_5795059 < baseStart_5795059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795076 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5795076 : Nat := 118140960795 + 5795076 * 2 ^ 59
def prefixEnd_5795076 : Nat := 4983230072969 + 3 ^ 40 * 5795076 * 2
def baseEnd_5795076 : Nat := 2975659417334673972198937

theorem tailTrace_5795076 : CollatzResearch.WordTrace tailWord_5795076 prefixEnd_5795076 2975659417334673972198937 := by
  unfold tailWord_5795076
  simp only [CollatzResearch.WordTrace]
  refine ⟨105681892976718423515130541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140909190635624564686840721 105681892976718423515130541)
  ·
    refine ⟨39630709866269408818173953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105681892976718423515130541 39630709866269408818173953)
    ·
      refine ⟨29723032399702056613630465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39630709866269408818173953 29723032399702056613630465)
      ·
        refine ⟨22292274299776542460222849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29723032399702056613630465 22292274299776542460222849)
        ·
          refine ⟨16719205724832406845167137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22292274299776542460222849 16719205724832406845167137)
          ·
            refine ⟨12539404293624305133875353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16719205724832406845167137 12539404293624305133875353)
            ·
              refine ⟨9404553220218228850406515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12539404293624305133875353 9404553220218228850406515)
              ·
                refine ⟨14106829830327343275609773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9404553220218228850406515 14106829830327343275609773)
                ·
                  refine ⟨5290061186372753728353665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14106829830327343275609773 5290061186372753728353665)
                  ·
                    refine ⟨3967545889779565296265249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290061186372753728353665 3967545889779565296265249)
                    ·
                      refine ⟨2975659417334673972198937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967545889779565296265249 2975659417334673972198937)
                      ·
                        rfl

theorem cell23_5795076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5795076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795076 prefixEnd_5795076 := by exact prefixLift 5795076
  have htrace : WordTrace (prefixWord ++ tailWord_5795076) baseStart_5795076 baseEnd_5795076 := by
    simpa [prefixWord, tailWord_5795076, baseEnd_5795076] using wordTrace_append hprefix tailTrace_5795076
  have hstable : (prefixWord ++ tailWord_5795076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795076).length < 2 ^ (prefixWord ++ tailWord_5795076).sum := by decide
  have hdescent : baseEnd_5795076 < baseStart_5795076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795145 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_5795145 : Nat := 118140960795 + 5795145 * 2 ^ 59
def prefixEnd_5795145 : Nat := 4983230072969 + 3 ^ 40 * 5795145 * 2
def baseEnd_5795145 : Nat := 2975694847499834202236119

theorem tailTrace_5795145 : CollatzResearch.WordTrace tailWord_5795145 prefixEnd_5795145 2975694847499834202236119 := by
  unfold tailWord_5795145
  simp only [CollatzResearch.WordTrace]
  refine ⟨211366302590186871814522889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140910868393457914543015259 211366302590186871814522889)
  ·
    refine ⟨158524726942640153860892167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211366302590186871814522889 158524726942640153860892167)
    ·
      refine ⟨237787090413960230791338251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158524726942640153860892167 237787090413960230791338251)
      ·
        refine ⟨356680635620940346187007377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237787090413960230791338251 356680635620940346187007377)
        ·
          refine ⟨267510476715705259640255533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356680635620940346187007377 267510476715705259640255533)
          ·
            refine ⟨100316428768389472365095825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267510476715705259640255533 100316428768389472365095825)
            ·
              refine ⟨75237321576292104273821869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100316428768389472365095825 75237321576292104273821869)
              ·
                refine ⟨28213995591109539102683201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75237321576292104273821869 28213995591109539102683201)
                ·
                  refine ⟨21160496693332154327012401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28213995591109539102683201 21160496693332154327012401)
                  ·
                    refine ⟨15870372519999115745259301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21160496693332154327012401 15870372519999115745259301)
                    ·
                      refine ⟨2975694847499834202236119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15870372519999115745259301 2975694847499834202236119)
                      ·
                        rfl

theorem cell23_5795145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_5795145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795145 prefixEnd_5795145 := by exact prefixLift 5795145
  have htrace : WordTrace (prefixWord ++ tailWord_5795145) baseStart_5795145 baseEnd_5795145 := by
    simpa [prefixWord, tailWord_5795145, baseEnd_5795145] using wordTrace_append hprefix tailTrace_5795145
  have hstable : (prefixWord ++ tailWord_5795145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795145).length < 2 ^ (prefixWord ++ tailWord_5795145).sum := by decide
  have hdescent : baseEnd_5795145 < baseStart_5795145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795195 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_5795195 : Nat := 118140960795 + 5795195 * 2 ^ 59
def prefixEnd_5795195 : Nat := 4983230072969 + 3 ^ 40 * 5795195 * 2
def baseEnd_5795195 : Nat := 2975720521532559006610889

theorem tailTrace_5795195 : CollatzResearch.WordTrace tailWord_5795195 prefixEnd_5795195 2975720521532559006610889 := by
  unfold tailWord_5795195
  simp only [CollatzResearch.WordTrace]
  refine ⟨211368126240005730353843039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140912084160003820235895359 211368126240005730353843039)
  ·
    refine ⟨317052189360008595530764559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211368126240005730353843039 317052189360008595530764559)
    ·
      refine ⟨475578284040012893296146839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317052189360008595530764559 475578284040012893296146839)
      ·
        refine ⟨713367426060019339944220259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475578284040012893296146839 713367426060019339944220259)
        ·
          refine ⟨1070051139090029009916330389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713367426060019339944220259 1070051139090029009916330389)
          ·
            refine ⟨50158647144845109839827987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1070051139090029009916330389 50158647144845109839827987)
            ·
              refine ⟨75237970717267664759741981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50158647144845109839827987 75237970717267664759741981)
              ·
                refine ⟨28214239018975374284903243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75237970717267664759741981 28214239018975374284903243)
                ·
                  refine ⟨42321358528463061427354865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28214239018975374284903243 42321358528463061427354865)
                  ·
                    refine ⟨31741018896347296070516149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42321358528463061427354865 31741018896347296070516149)
                    ·
                      refine ⟨2975720521532559006610889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31741018896347296070516149 2975720521532559006610889)
                      ·
                        rfl

theorem cell23_5795195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_5795195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795195 prefixEnd_5795195 := by exact prefixLift 5795195
  have htrace : WordTrace (prefixWord ++ tailWord_5795195) baseStart_5795195 baseEnd_5795195 := by
    simpa [prefixWord, tailWord_5795195, baseEnd_5795195] using wordTrace_append hprefix tailTrace_5795195
  have hstable : (prefixWord ++ tailWord_5795195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795195).length < 2 ^ (prefixWord ++ tailWord_5795195).sum := by decide
  have hdescent : baseEnd_5795195 < baseStart_5795195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795232 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_5795232 : Nat := 118140960795 + 5795232 * 2 ^ 59
def prefixEnd_5795232 : Nat := 4983230072969 + 3 ^ 40 * 5795232 * 2
def baseEnd_5795232 : Nat := 991913173438925120616073

theorem tailTrace_5795232 : CollatzResearch.WordTrace tailWord_5795232 prefixEnd_5795232 991913173438925120616073 := by
  unfold tailWord_5795232
  simp only [CollatzResearch.WordTrace]
  refine ⟨105684737870435842836469975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140912983827247790448626633 105684737870435842836469975)
  ·
    refine ⟨158527106805653764254704963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105684737870435842836469975 158527106805653764254704963)
    ·
      refine ⟨237790660208480646382057445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158527106805653764254704963 237790660208480646382057445)
      ·
        refine ⟨44585748789090121196635771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237790660208480646382057445 44585748789090121196635771)
        ·
          refine ⟨66878623183635181794953657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44585748789090121196635771 66878623183635181794953657)
          ·
            refine ⟨50158967387726386346215243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66878623183635181794953657 50158967387726386346215243)
            ·
              refine ⟨75238451081589579519322865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50158967387726386346215243 75238451081589579519322865)
              ·
                refine ⟨56428838311192184639492149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75238451081589579519322865 56428838311192184639492149)
                ·
                  refine ⟨5290203591674267309952389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56428838311192184639492149 5290203591674267309952389)
                  ·
                    refine ⟨991913173438925120616073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290203591674267309952389 991913173438925120616073)
                    ·
                      rfl

theorem cell23_5795232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_5795232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795232 prefixEnd_5795232 := by exact prefixLift 5795232
  have htrace : WordTrace (prefixWord ++ tailWord_5795232) baseStart_5795232 baseEnd_5795232 := by
    simpa [prefixWord, tailWord_5795232, baseEnd_5795232] using wordTrace_append hprefix tailTrace_5795232
  have hstable : (prefixWord ++ tailWord_5795232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795232).length < 2 ^ (prefixWord ++ tailWord_5795232).sum := by decide
  have hdescent : baseEnd_5795232 < baseStart_5795232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795235 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_5795235 : Nat := 118140960795 + 5795235 * 2 ^ 59
def prefixEnd_5795235 : Nat := 4983230072969 + 3 ^ 40 * 5795235 * 2
def baseEnd_5795235 : Nat := 2975741060758738850110705

theorem tailTrace_5795235 : CollatzResearch.WordTrace tailWord_5795235 prefixEnd_5795235 2975741060758738850110705 := by
  unfold tailWord_5795235
  simp only [CollatzResearch.WordTrace]
  refine ⟨211369585159860817185299159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140913056773240544790199439 211369585159860817185299159)
  ·
    refine ⟨317054377739791225777948739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211369585159860817185299159 317054377739791225777948739)
    ·
      refine ⟨475581566609686838666923109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317054377739791225777948739 475581566609686838666923109)
      ·
        refine ⟨89171543739316282250048083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 475581566609686838666923109 89171543739316282250048083)
        ·
          refine ⟨133757315608974423375072125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89171543739316282250048083 133757315608974423375072125)
          ·
            refine ⟨50158993353365408765652047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133757315608974423375072125 50158993353365408765652047)
            ·
              refine ⟨75238490030048113148478071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50158993353365408765652047 75238490030048113148478071)
              ·
                refine ⟨112857735045072169722717107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75238490030048113148478071 112857735045072169722717107)
                ·
                  refine ⟨169286602567608254584075661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112857735045072169722717107 169286602567608254584075661)
                  ·
                    refine ⟨63482475962853095469028373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169286602567608254584075661 63482475962853095469028373)
                    ·
                      refine ⟨2975741060758738850110705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63482475962853095469028373 2975741060758738850110705)
                      ·
                        rfl

theorem cell23_5795235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_5795235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795235 prefixEnd_5795235 := by exact prefixLift 5795235
  have htrace : WordTrace (prefixWord ++ tailWord_5795235) baseStart_5795235 baseEnd_5795235 := by
    simpa [prefixWord, tailWord_5795235, baseEnd_5795235] using wordTrace_append hprefix tailTrace_5795235
  have hstable : (prefixWord ++ tailWord_5795235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795235).length < 2 ^ (prefixWord ++ tailWord_5795235).sum := by decide
  have hdescent : baseEnd_5795235 < baseStart_5795235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795239 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5795239 : Nat := 118140960795 + 5795239 * 2 ^ 59
def prefixEnd_5795239 : Nat := 4983230072969 + 3 ^ 40 * 5795239 * 2
def baseEnd_5795239 : Nat := 2975743114681356834460687

theorem tailTrace_5795239 : CollatzResearch.WordTrace tailWord_5795239 prefixEnd_5795239 2975743114681356834460687 := by
  unfold tailWord_5795239
  simp only [CollatzResearch.WordTrace]
  refine ⟨211369731051846325868444771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140913154034564217245629847 211369731051846325868444771)
  ·
    refine ⟨317054596577769488802667157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211369731051846325868444771 317054596577769488802667157)
    ·
      refine ⟨14861934214582944787625023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317054596577769488802667157 14861934214582944787625023)
      ·
        refine ⟨22292901321874417181437535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14861934214582944787625023 22292901321874417181437535)
        ·
          refine ⟨33439351982811625772156303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22292901321874417181437535 33439351982811625772156303)
          ·
            refine ⟨50159027974217438658234455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33439351982811625772156303 50159027974217438658234455)
            ·
              refine ⟨75238541961326157987351683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50159027974217438658234455 75238541961326157987351683)
              ·
                refine ⟨112857812941989236981027525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75238541961326157987351683 112857812941989236981027525)
                ·
                  refine ⟨21160839926622981933942661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112857812941989236981027525 21160839926622981933942661)
                  ·
                    refine ⟨3967657486241809112614249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21160839926622981933942661 3967657486241809112614249)
                    ·
                      refine ⟨2975743114681356834460687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967657486241809112614249 2975743114681356834460687)
                      ·
                        rfl

theorem cell23_5795239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5795239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795239 prefixEnd_5795239 := by exact prefixLift 5795239
  have htrace : WordTrace (prefixWord ++ tailWord_5795239) baseStart_5795239 baseEnd_5795239 := by
    simpa [prefixWord, tailWord_5795239, baseEnd_5795239] using wordTrace_append hprefix tailTrace_5795239
  have hstable : (prefixWord ++ tailWord_5795239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795239).length < 2 ^ (prefixWord ++ tailWord_5795239).sum := by decide
  have hdescent : baseEnd_5795239 < baseStart_5795239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795249 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_5795249 : Nat := 118140960795 + 5795249 * 2 ^ 59
def prefixEnd_5795249 : Nat := 4983230072969 + 3 ^ 40 * 5795249 * 2
def baseEnd_5795249 : Nat := 991916083162633931778547

theorem tailTrace_5795249 : CollatzResearch.WordTrace tailWord_5795249 prefixEnd_5795249 991916083162633931778547 := by
  unfold tailWord_5795249
  simp only [CollatzResearch.WordTrace]
  refine ⟨211370095781810097576308801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140913397187873398384205867 211370095781810097576308801)
  ·
    refine ⟨158527571836357573182231601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211370095781810097576308801 158527571836357573182231601)
    ·
      refine ⟨118895678877268179886673701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158527571836357573182231601 118895678877268179886673701)
      ·
        refine ⟨22292939789487783728751319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118895678877268179886673701 22292939789487783728751319)
        ·
          refine ⟨33439409684231675593126979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22292939789487783728751319 33439409684231675593126979)
          ·
            refine ⟨50159114526347513389690469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33439409684231675593126979 50159114526347513389690469)
            ·
              refine ⟨9404833973690158760566963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50159114526347513389690469 9404833973690158760566963)
              ·
                refine ⟨14107250960535238140850445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9404833973690158760566963 14107250960535238140850445)
                ·
                  refine ⟨5290219110200714302818917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14107250960535238140850445 5290219110200714302818917)
                  ·
                    refine ⟨991916083162633931778547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290219110200714302818917 991916083162633931778547)
                    ·
                      rfl

theorem cell23_5795249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_5795249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795249 prefixEnd_5795249 := by exact prefixLift 5795249
  have htrace : WordTrace (prefixWord ++ tailWord_5795249) baseStart_5795249 baseEnd_5795249 := by
    simpa [prefixWord, tailWord_5795249, baseEnd_5795249] using wordTrace_append hprefix tailTrace_5795249
  have hstable : (prefixWord ++ tailWord_5795249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795249).length < 2 ^ (prefixWord ++ tailWord_5795249).sum := by decide
  have hdescent : baseEnd_5795249 < baseStart_5795249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795272 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_5795272 : Nat := 118140960795 + 5795272 * 2 ^ 59
def prefixEnd_5795272 : Nat := 4983230072969 + 3 ^ 40 * 5795272 * 2
def baseEnd_5795272 : Nat := 2975760059542955205348035

theorem tailTrace_5795272 : CollatzResearch.WordTrace tailWord_5795272 prefixEnd_5795272 2975760059542955205348035 := by
  unfold tailWord_5795272
  simp only [CollatzResearch.WordTrace]
  refine ⟨105685467330363386252198035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140913956440484515002930713 105685467330363386252198035)
  ·
    refine ⟨158528200995545079378297053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105685467330363386252198035 158528200995545079378297053)
    ·
      refine ⟨59448075373329404766861395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158528200995545079378297053 59448075373329404766861395)
      ·
        refine ⟨89172113059994107150292093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59448075373329404766861395 89172113059994107150292093)
        ·
          refine ⟨33439542397497790181359535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89172113059994107150292093 33439542397497790181359535)
          ·
            refine ⟨50159313596246685272039303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33439542397497790181359535 50159313596246685272039303)
            ·
              refine ⟨75238970394370027908058955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50159313596246685272039303 75238970394370027908058955)
              ·
                refine ⟨112858455591555041862088433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75238970394370027908058955 112858455591555041862088433)
                ·
                  refine ⟨84643841693666281396566325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112858455591555041862088433 84643841693666281396566325)
                  ·
                    refine ⟨7935360158781213880928093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84643841693666281396566325 7935360158781213880928093)
                    ·
                      refine ⟨2975760059542955205348035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7935360158781213880928093 2975760059542955205348035)
                      ·
                        rfl

theorem cell23_5795272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_5795272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795272 prefixEnd_5795272 := by exact prefixLift 5795272
  have htrace : WordTrace (prefixWord ++ tailWord_5795272) baseStart_5795272 baseEnd_5795272 := by
    simpa [prefixWord, tailWord_5795272, baseEnd_5795272] using wordTrace_append hprefix tailTrace_5795272
  have hstable : (prefixWord ++ tailWord_5795272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795272).length < 2 ^ (prefixWord ++ tailWord_5795272).sum := by decide
  have hdescent : baseEnd_5795272 < baseStart_5795272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795322 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_5795322 : Nat := 118140960795 + 5795322 * 2 ^ 59
def prefixEnd_5795322 : Nat := 4983230072969 + 3 ^ 40 * 5795322 * 2
def baseEnd_5795322 : Nat := 991928577858560003240935

theorem tailTrace_5795322 : CollatzResearch.WordTrace tailWord_5795322 prefixEnd_5795322 991928577858560003240935 := by
  unfold tailWord_5795322
  simp only [CollatzResearch.WordTrace]
  refine ⟨52843189577636407760929055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140915172207030420695810813 52843189577636407760929055)
  ·
    refine ⟨79264784366454611641393583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52843189577636407760929055 79264784366454611641393583)
    ·
      refine ⟨118897176549681917462090375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79264784366454611641393583 118897176549681917462090375)
      ·
        refine ⟨178345764824522876193135563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118897176549681917462090375 178345764824522876193135563)
        ·
          refine ⟨267518647236784314289703345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178345764824522876193135563 267518647236784314289703345)
          ·
            refine ⟨200638985427588235717277509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267518647236784314289703345 200638985427588235717277509)
            ·
              refine ⟨37619809767672794196989533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200638985427588235717277509 37619809767672794196989533)
              ·
                refine ⟨14107428662877297823871075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37619809767672794196989533 14107428662877297823871075)
                ·
                  refine ⟨21161142994315946735806613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14107428662877297823871075 21161142994315946735806613)
                  ·
                    refine ⟨991928577858560003240935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21161142994315946735806613 991928577858560003240935)
                    ·
                      rfl

theorem cell23_5795322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_5795322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795322 prefixEnd_5795322 := by exact prefixLift 5795322
  have htrace : WordTrace (prefixWord ++ tailWord_5795322) baseStart_5795322 baseEnd_5795322 := by
    simpa [prefixWord, tailWord_5795322, baseEnd_5795322] using wordTrace_append hprefix tailTrace_5795322
  have hstable : (prefixWord ++ tailWord_5795322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795322).length < 2 ^ (prefixWord ++ tailWord_5795322).sum := by decide
  have hdescent : baseEnd_5795322 < baseStart_5795322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795339 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 1, 6]
def baseStart_5795339 : Nat := 118140960795 + 5795339 * 2 ^ 59
def prefixEnd_5795339 : Nat := 4983230072969 + 3 ^ 40 * 5795339 * 2
def baseEnd_5795339 : Nat := 991931487582268814403409

theorem tailTrace_5795339 : CollatzResearch.WordTrace tailWord_5795339 prefixEnd_5795339 991931487582268814403409 := by
  unfold tailWord_5795339
  simp only [CollatzResearch.WordTrace]
  refine ⟨211373378351484042947085071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140915585567656028631390047 211373378351484042947085071)
  ·
    refine ⟨317060067527226064420627607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211373378351484042947085071 317060067527226064420627607)
    ·
      refine ⟨475590101290839096630941411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317060067527226064420627607 475590101290839096630941411)
      ·
        refine ⟨713385151936258644946412117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475590101290839096630941411 713385151936258644946412117)
        ·
          refine ⟨8359982249253030995465767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 713385151936258644946412117 8359982249253030995465767)
          ·
            refine ⟨12539973373879546493198651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359982249253030995465767 12539973373879546493198651)
            ·
              refine ⟨18809960060819319739797977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12539973373879546493198651 18809960060819319739797977)
              ·
                refine ⟨14107470045614489804848483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18809960060819319739797977 14107470045614489804848483)
                ·
                  refine ⟨21161205068421734707272725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14107470045614489804848483 21161205068421734707272725)
                  ·
                    refine ⟨991931487582268814403409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21161205068421734707272725 991931487582268814403409)
                    ·
                      rfl

theorem cell23_5795339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 6].length) (baseStart_5795339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795339 prefixEnd_5795339 := by exact prefixLift 5795339
  have htrace : WordTrace (prefixWord ++ tailWord_5795339) baseStart_5795339 baseEnd_5795339 := by
    simpa [prefixWord, tailWord_5795339, baseEnd_5795339] using wordTrace_append hprefix tailTrace_5795339
  have hstable : (prefixWord ++ tailWord_5795339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795339).length < 2 ^ (prefixWord ++ tailWord_5795339).sum := by decide
  have hdescent : baseEnd_5795339 < baseStart_5795339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795349 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_5795349 : Nat := 118140960795 + 5795349 * 2 ^ 59
def prefixEnd_5795349 : Nat := 4983230072969 + 3 ^ 40 * 5795349 * 2
def baseEnd_5795349 : Nat := 2975799597553351404085181

theorem tailTrace_5795349 : CollatzResearch.WordTrace tailWord_5795349 prefixEnd_5795349 2975799597553351404085181 := by
  unfold tailWord_5795349
  simp only [CollatzResearch.WordTrace]
  refine ⟨211373743081447814654949101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140915828720965209769966067 211373743081447814654949101)
  ·
    refine ⟨79265153655542930495605913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211373743081447814654949101 79265153655542930495605913)
    ·
      refine ⟨59448865241657197871704435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79265153655542930495605913 59448865241657197871704435)
      ·
        refine ⟨89173297862485796807556653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59448865241657197871704435 89173297862485796807556653)
        ·
          refine ⟨33439986698432173802833745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89173297862485796807556653 33439986698432173802833745)
          ·
            refine ⟨25079990023824130352125309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33439986698432173802833745 25079990023824130352125309)
            ·
              refine ⟨9404996258934048882046991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25079990023824130352125309 9404996258934048882046991)
              ·
                refine ⟨14107494388401073323070487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9404996258934048882046991 14107494388401073323070487)
                ·
                  refine ⟨21161241582601609984605731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14107494388401073323070487 21161241582601609984605731)
                  ·
                    refine ⟨31741862373902414976908597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21161241582601609984605731 31741862373902414976908597)
                    ·
                      refine ⟨2975799597553351404085181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31741862373902414976908597 2975799597553351404085181)
                      ·
                        rfl

theorem cell23_5795349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_5795349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795349 prefixEnd_5795349 := by exact prefixLift 5795349
  have htrace : WordTrace (prefixWord ++ tailWord_5795349) baseStart_5795349 baseEnd_5795349 := by
    simpa [prefixWord, tailWord_5795349, baseEnd_5795349] using wordTrace_append hprefix tailTrace_5795349
  have hstable : (prefixWord ++ tailWord_5795349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795349).length < 2 ^ (prefixWord ++ tailWord_5795349).sum := by decide
  have hdescent : baseEnd_5795349 < baseStart_5795349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795352 : List Nat := [2, 1, 2, 3, 4, 11]
def baseStart_5795352 : Nat := 118140960795 + 5795352 * 2 ^ 59
def prefixEnd_5795352 : Nat := 4983230072969 + 3 ^ 40 * 5795352 * 2
def baseEnd_5795352 : Nat := 12246095218087715606369

theorem tailTrace_5795352 : CollatzResearch.WordTrace tailWord_5795352 prefixEnd_5795352 12246095218087715606369 := by
  unfold tailWord_5795352
  simp only [CollatzResearch.WordTrace]
  refine ⟨105686926250218473083654155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140915901666957964111538873 105686926250218473083654155)
  ·
    refine ⟨158530389375327709625481233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105686926250218473083654155 158530389375327709625481233)
    ·
      refine ⟨118897792031495782219110925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158530389375327709625481233 118897792031495782219110925)
      ·
        refine ⟨44586672011810918332166597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118897792031495782219110925 44586672011810918332166597)
        ·
          refine ⟨8360001002214547187281237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44586672011810918332166597 8360001002214547187281237)
          ·
            refine ⟨12246095218087715606369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8360001002214547187281237 12246095218087715606369)
            ·
              rfl

theorem cell23_5795352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 11].length) (baseStart_5795352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795352 prefixEnd_5795352 := by exact prefixLift 5795352
  have htrace : WordTrace (prefixWord ++ tailWord_5795352) baseStart_5795352 baseEnd_5795352 := by
    simpa [prefixWord, tailWord_5795352, baseEnd_5795352] using wordTrace_append hprefix tailTrace_5795352
  have hstable : (prefixWord ++ tailWord_5795352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795352).length < 2 ^ (prefixWord ++ tailWord_5795352).sum := by decide
  have hdescent : baseEnd_5795352 < baseStart_5795352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795356 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_5795356 : Nat := 118140960795 + 5795356 * 2 ^ 59
def prefixEnd_5795356 : Nat := 4983230072969 + 3 ^ 40 * 5795356 * 2
def baseEnd_5795356 : Nat := 991934397305977625565883

theorem tailTrace_5795356 : CollatzResearch.WordTrace tailWord_5795356 prefixEnd_5795356 991934397305977625565883 := by
  unfold tailWord_5795356
  simp only [CollatzResearch.WordTrace]
  refine ⟨105686999196211227425226961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140915998928281636566969281 105686999196211227425226961)
  ·
    refine ⟨79265249397158420568920221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105686999196211227425226961 79265249397158420568920221)
    ·
      refine ⟨29724468523934407713345083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79265249397158420568920221 29724468523934407713345083)
      ·
        refine ⟨44586702785901611570017625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29724468523934407713345083 44586702785901611570017625)
        ·
          refine ⟨33440027089426208677513219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44586702785901611570017625 33440027089426208677513219)
          ·
            refine ⟨50160040634139313016269829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33440027089426208677513219 50160040634139313016269829)
            ·
              refine ⟨9405007618901121190550593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50160040634139313016269829 9405007618901121190550593)
              ·
                refine ⟨7053755714175840892912945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9405007618901121190550593 7053755714175840892912945)
                ·
                  refine ⟨5290316785631880669684709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053755714175840892912945 5290316785631880669684709)
                  ·
                    refine ⟨991934397305977625565883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290316785631880669684709 991934397305977625565883)
                    ·
                      rfl

theorem cell23_5795356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_5795356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795356 prefixEnd_5795356 := by exact prefixLift 5795356
  have htrace : WordTrace (prefixWord ++ tailWord_5795356) baseStart_5795356 baseEnd_5795356 := by
    simpa [prefixWord, tailWord_5795356, baseEnd_5795356] using wordTrace_append hprefix tailTrace_5795356
  have hstable : (prefixWord ++ tailWord_5795356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795356).length < 2 ^ (prefixWord ++ tailWord_5795356).sum := by decide
  have hdescent : baseEnd_5795356 < baseStart_5795356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795379 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3]
def baseStart_5795379 : Nat := 118140960795 + 5795379 * 2 ^ 59
def prefixEnd_5795379 : Nat := 4983230072969 + 3 ^ 40 * 5795379 * 2
def baseEnd_5795379 : Nat := 2975815001972986286710043

theorem tailTrace_5795379 : CollatzResearch.WordTrace tailWord_5795379 prefixEnd_5795379 2975815001972986286710043 := by
  unfold tailWord_5795379
  simp only [CollatzResearch.WordTrace]
  refine ⟨211374837271339129778541191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140916558180892753185694127 211374837271339129778541191)
  ·
    refine ⟨317062255907008694667811787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211374837271339129778541191 317062255907008694667811787)
    ·
      refine ⟨475593383860513042001717681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317062255907008694667811787 475593383860513042001717681)
      ·
        refine ⟨356695037895384781501288261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475593383860513042001717681 356695037895384781501288261)
        ·
          refine ⟨66880319605384646531491549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356695037895384781501288261 66880319605384646531491549)
          ·
            refine ⟨25080119852019242449309331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66880319605384646531491549 25080119852019242449309331)
            ·
              refine ⟨37620179778028863673963997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25080119852019242449309331 37620179778028863673963997)
              ·
                refine ⟨14107567416760823877736499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37620179778028863673963997 14107567416760823877736499)
                ·
                  refine ⟨21161351125141235816604749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14107567416760823877736499 21161351125141235816604749)
                  ·
                    refine ⟨7935506671927963431226781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21161351125141235816604749 7935506671927963431226781)
                    ·
                      refine ⟨2975815001972986286710043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7935506671927963431226781 2975815001972986286710043)
                      ·
                        rfl

theorem cell23_5795379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_5795379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795379 prefixEnd_5795379 := by exact prefixLift 5795379
  have htrace : WordTrace (prefixWord ++ tailWord_5795379) baseStart_5795379 baseEnd_5795379 := by
    simpa [prefixWord, tailWord_5795379, baseEnd_5795379] using wordTrace_append hprefix tailTrace_5795379
  have hstable : (prefixWord ++ tailWord_5795379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795379).length < 2 ^ (prefixWord ++ tailWord_5795379).sum := by decide
  have hdescent : baseEnd_5795379 < baseStart_5795379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795392 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_5795392 : Nat := 118140960795 + 5795392 * 2 ^ 59
def prefixEnd_5795392 : Nat := 4983230072969 + 3 ^ 40 * 5795392 * 2
def baseEnd_5795392 : Nat := 2975821677221494735847483

theorem tailTrace_5795392 : CollatzResearch.WordTrace tailWord_5795392 prefixEnd_5795392 2975821677221494735847483 := by
  unfold tailWord_5795392
  simp only [CollatzResearch.WordTrace]
  refine ⟨105687655710146016499382215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140916874280194688665842953 105687655710146016499382215)
  ·
    refine ⟨158531483565219024749073323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105687655710146016499382215 158531483565219024749073323)
    ·
      refine ⟨237797225347828537123609985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158531483565219024749073323 237797225347828537123609985)
      ·
        refine ⟨178347919010871402842707489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237797225347828537123609985 178347919010871402842707489)
        ·
          refine ⟨133760939258153552132030617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178347919010871402842707489 133760939258153552132030617)
          ·
            refine ⟨100320704443615164099022963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133760939258153552132030617 100320704443615164099022963)
            ·
              refine ⟨150481056665422746148534445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100320704443615164099022963 150481056665422746148534445)
              ·
                refine ⟨56430396249533529805700417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150481056665422746148534445 56430396249533529805700417)
                ·
                  refine ⟨42322797187150147354275313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56430396249533529805700417 42322797187150147354275313)
                  ·
                    refine ⟨31742097890362610515706485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42322797187150147354275313 31742097890362610515706485)
                    ·
                      refine ⟨2975821677221494735847483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31742097890362610515706485 2975821677221494735847483)
                      ·
                        rfl

theorem cell23_5795392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_5795392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795392 prefixEnd_5795392 := by exact prefixLift 5795392
  have htrace : WordTrace (prefixWord ++ tailWord_5795392) baseStart_5795392 baseEnd_5795392 := by
    simpa [prefixWord, tailWord_5795392, baseEnd_5795392] using wordTrace_append hprefix tailTrace_5795392
  have hstable : (prefixWord ++ tailWord_5795392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795392).length < 2 ^ (prefixWord ++ tailWord_5795392).sum := by decide
  have hdescent : baseEnd_5795392 < baseStart_5795392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795414 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5795414 : Nat := 118140960795 + 5795414 * 2 ^ 59
def prefixEnd_5795414 : Nat := 4983230072969 + 3 ^ 40 * 5795414 * 2
def baseEnd_5795414 : Nat := 2975832973795893649772383

theorem tailTrace_5795414 : CollatzResearch.WordTrace tailWord_5795414 prefixEnd_5795414 2975832973795893649772383 := by
  unfold tailWord_5795414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211007114138270672254081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140917409217474887170710197 13211007114138270672254081)
  ·
    refine ⟨9908255335603703004190561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13211007114138270672254081 9908255335603703004190561)
    ·
      refine ⟨7431191501702777253142921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9908255335603703004190561 7431191501702777253142921)
      ·
        refine ⟨5573393626277082939857191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7431191501702777253142921 5573393626277082939857191)
        ·
          refine ⟨8360090439415624409785787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573393626277082939857191 8360090439415624409785787)
          ·
            refine ⟨12540135659123436614678681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360090439415624409785787 12540135659123436614678681)
            ·
              refine ⟨9405101744342577461009011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12540135659123436614678681 9405101744342577461009011)
              ·
                refine ⟨14107652616513866191513517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9405101744342577461009011 14107652616513866191513517)
                ·
                  refine ⟨5290369731192699821817569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14107652616513866191513517 5290369731192699821817569)
                  ·
                    refine ⟨3967777298394524866363177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290369731192699821817569 3967777298394524866363177)
                    ·
                      refine ⟨2975832973795893649772383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967777298394524866363177 2975832973795893649772383)
                      ·
                        rfl

theorem cell23_5795414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5795414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795414 prefixEnd_5795414 := by exact prefixLift 5795414
  have htrace : WordTrace (prefixWord ++ tailWord_5795414) baseStart_5795414 baseEnd_5795414 := by
    simpa [prefixWord, tailWord_5795414, baseEnd_5795414] using wordTrace_append hprefix tailTrace_5795414
  have hstable : (prefixWord ++ tailWord_5795414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795414).length < 2 ^ (prefixWord ++ tailWord_5795414).sum := by decide
  have hdescent : baseEnd_5795414 < baseStart_5795414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795429 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_5795429 : Nat := 118140960795 + 5795429 * 2 ^ 59
def prefixEnd_5795429 : Nat := 4983230072969 + 3 ^ 40 * 5795429 * 2
def baseEnd_5795429 : Nat := 991946892001903697028271

theorem tailTrace_5795429 : CollatzResearch.WordTrace tailWord_5795429 prefixEnd_5795429 991946892001903697028271 := by
  unfold tailWord_5795429
  simp only [CollatzResearch.WordTrace]
  refine ⟨211376660921157988317861341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140917773947438658878574227 211376660921157988317861341)
  ·
    refine ⟨79266247845434245619198003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211376660921157988317861341 79266247845434245619198003)
    ·
      refine ⟨118899371768151368428797005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79266247845434245619198003 118899371768151368428797005)
      ·
        refine ⟨44587264413056763160798877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118899371768151368428797005 44587264413056763160798877)
        ·
          refine ⟨16720224154896286185299579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44587264413056763160798877 16720224154896286185299579)
          ·
            refine ⟨25080336232344429277949369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16720224154896286185299579 25080336232344429277949369)
            ·
              refine ⟨18810252174258321958462027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25080336232344429277949369 18810252174258321958462027)
              ·
                refine ⟨28215378261387482937693041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18810252174258321958462027 28215378261387482937693041)
                ·
                  refine ⟨21161533696040612203269781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28215378261387482937693041 21161533696040612203269781)
                  ·
                    refine ⟨991946892001903697028271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21161533696040612203269781 991946892001903697028271)
                    ·
                      rfl

theorem cell23_5795429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_5795429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795429 prefixEnd_5795429 := by exact prefixLift 5795429
  have htrace : WordTrace (prefixWord ++ tailWord_5795429) baseStart_5795429 baseEnd_5795429 := by
    simpa [prefixWord, tailWord_5795429, baseEnd_5795429] using wordTrace_append hprefix tailTrace_5795429
  have hstable : (prefixWord ++ tailWord_5795429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795429).length < 2 ^ (prefixWord ++ tailWord_5795429).sum := by decide
  have hdescent : baseEnd_5795429 < baseStart_5795429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795453 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_5795453 : Nat := 118140960795 + 5795453 * 2 ^ 59
def prefixEnd_5795453 : Nat := 4983230072969 + 3 ^ 40 * 5795453 * 2
def baseEnd_5795453 : Nat := 2975852999541418997184703

theorem tailTrace_5795453 : CollatzResearch.WordTrace tailWord_5795453 prefixEnd_5795453 2975852999541418997184703 := by
  unfold tailWord_5795453
  simp only [CollatzResearch.WordTrace]
  refine ⟨211377536273071040416735013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140918357515380693611156675 211377536273071040416735013)
  ·
    refine ⟨39633288051200820078137815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211377536273071040416735013 39633288051200820078137815)
    ·
      refine ⟨59449932076801230117206723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39633288051200820078137815 59449932076801230117206723)
      ·
        refine ⟨89174898115201845175810085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59449932076801230117206723 89174898115201845175810085)
        ·
          refine ⟨16720293396600345970464391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89174898115201845175810085 16720293396600345970464391)
          ·
            refine ⟨25080440094900518955696587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16720293396600345970464391 25080440094900518955696587)
            ·
              refine ⟨37620660142350778433544881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25080440094900518955696587 37620660142350778433544881)
              ·
                refine ⟨28215495106763083825158661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37620660142350778433544881 28215495106763083825158661)
                ·
                  refine ⟨5290405332518078217217249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28215495106763083825158661 5290405332518078217217249)
                  ·
                    refine ⟨3967803999388558662912937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290405332518078217217249 3967803999388558662912937)
                    ·
                      refine ⟨2975852999541418997184703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967803999388558662912937 2975852999541418997184703)
                      ·
                        rfl

theorem cell23_5795453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_5795453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795453 prefixEnd_5795453 := by exact prefixLift 5795453
  have htrace : WordTrace (prefixWord ++ tailWord_5795453) baseStart_5795453 baseEnd_5795453 := by
    simpa [prefixWord, tailWord_5795453, baseEnd_5795453] using wordTrace_append hprefix tailTrace_5795453
  have hstable : (prefixWord ++ tailWord_5795453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795453).length < 2 ^ (prefixWord ++ tailWord_5795453).sum := by decide
  have hdescent : baseEnd_5795453 < baseStart_5795453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795487 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5795487 : Nat := 118140960795 + 5795487 * 2 ^ 59
def prefixEnd_5795487 : Nat := 4983230072969 + 3 ^ 40 * 5795487 * 2
def baseEnd_5795487 : Nat := 2975870457883671864159547

theorem tailTrace_5795487 : CollatzResearch.WordTrace tailWord_5795487 prefixEnd_5795487 2975870457883671864159547 := by
  unfold tailWord_5795487
  simp only [CollatzResearch.WordTrace]
  refine ⟨211378776354947864223472715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140919184236631909482315143 211378776354947864223472715)
  ·
    refine ⟨317068164532421796335209073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211378776354947864223472715 317068164532421796335209073)
    ·
      refine ⟨237801123399316347251406805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317068164532421796335209073 237801123399316347251406805)
      ·
        refine ⟨5573463829671476888704847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 237801123399316347251406805 5573463829671476888704847)
        ·
          refine ⟨8360195744507215333057271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573463829671476888704847 8360195744507215333057271)
          ·
            refine ⟨12540293616760822999585907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360195744507215333057271 12540293616760822999585907)
            ·
              refine ⟨18810440425141234499378861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12540293616760822999585907 18810440425141234499378861)
              ·
                refine ⟨7053915159427962937267073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18810440425141234499378861 7053915159427962937267073)
                ·
                  refine ⟨5290436369570972202950305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053915159427962937267073 5290436369570972202950305)
                  ·
                    refine ⟨3967827277178229152212729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290436369570972202950305 3967827277178229152212729)
                    ·
                      refine ⟨2975870457883671864159547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3967827277178229152212729 2975870457883671864159547)
                      ·
                        rfl

theorem cell23_5795487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5795487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795487 prefixEnd_5795487 := by exact prefixLift 5795487
  have htrace : WordTrace (prefixWord ++ tailWord_5795487) baseStart_5795487 baseEnd_5795487 := by
    simpa [prefixWord, tailWord_5795487, baseEnd_5795487] using wordTrace_append hprefix tailTrace_5795487
  have hstable : (prefixWord ++ tailWord_5795487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795487).length < 2 ^ (prefixWord ++ tailWord_5795487).sum := by decide
  have hdescent : baseEnd_5795487 < baseStart_5795487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795533 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5795533 : Nat := 118140960795 + 5795533 * 2 ^ 59
def prefixEnd_5795533 : Nat := 4983230072969 + 3 ^ 40 * 5795533 * 2
def baseEnd_5795533 : Nat := 2975894077993778684184335

theorem tailTrace_5795533 : CollatzResearch.WordTrace tailWord_5795533 prefixEnd_5795533 2975894077993778684184335 := by
  unfold tailWord_5795533
  simp only [CollatzResearch.WordTrace]
  refine ⟨211380454112781214079647253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140920302741854142719764835 211380454112781214079647253)
  ·
    refine ⟨9908458786536619409983465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211380454112781214079647253 9908458786536619409983465)
    ·
      refine ⟨7431344089902464557487599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9908458786536619409983465 7431344089902464557487599)
      ·
        refine ⟨11147016134853696836231399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7431344089902464557487599 11147016134853696836231399)
        ·
          refine ⟨16720524202280545254347099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11147016134853696836231399 16720524202280545254347099)
          ·
            refine ⟨25080786303420817881520649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16720524202280545254347099 25080786303420817881520649)
            ·
              refine ⟨18810589727565613411140487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25080786303420817881520649 18810589727565613411140487)
              ·
                refine ⟨28215884591348420116710731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18810589727565613411140487 28215884591348420116710731)
                ·
                  refine ⟨42323826887022630175066097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28215884591348420116710731 42323826887022630175066097)
                  ·
                    refine ⟨31742870165266972631299573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42323826887022630175066097 31742870165266972631299573)
                    ·
                      refine ⟨2975894077993778684184335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31742870165266972631299573 2975894077993778684184335)
                      ·
                        rfl

theorem cell23_5795533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5795533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795533 prefixEnd_5795533 := by exact prefixLift 5795533
  have htrace : WordTrace (prefixWord ++ tailWord_5795533) baseStart_5795533 baseEnd_5795533 := by
    simpa [prefixWord, tailWord_5795533, baseEnd_5795533] using wordTrace_append hprefix tailTrace_5795533
  have hstable : (prefixWord ++ tailWord_5795533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795533).length < 2 ^ (prefixWord ++ tailWord_5795533).sum := by decide
  have hdescent : baseEnd_5795533 < baseStart_5795533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
