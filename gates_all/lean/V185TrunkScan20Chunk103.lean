import V185TrunkScan20Chunk102

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_626458 : List Nat := [3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_626458 : Nat := 118140960795 + 626458 * 2 ^ 59
def prefixEnd_626458 : Nat := 4983230072969 + 3 ^ 40 * 626458 * 2
def baseEnd_626458 : Nat := 95310833734641544857475

theorem tailTrace_626458 : CollatzResearch.WordTrace tailWord_626458 prefixEnd_626458 95310833734641544857475 := by
  unfold tailWord_626458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712200091114282838390007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15232533576304754235706685 5712200091114282838390007)
  ·
    refine ⟨8568300136671424257585011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5712200091114282838390007 8568300136671424257585011)
    ·
      refine ⟨12852450205007136386377517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8568300136671424257585011 12852450205007136386377517)
      ·
        refine ⟨4819668826877676144891569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12852450205007136386377517 4819668826877676144891569)
        ·
          refine ⟨3614751620158257108668677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4819668826877676144891569 3614751620158257108668677)
          ·
            refine ⟨677765928779673207875377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3614751620158257108668677 677765928779673207875377)
            ·
              refine ⟨508324446584754905906533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677765928779673207875377 508324446584754905906533)
              ·
                refine ⟨95310833734641544857475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508324446584754905906533 95310833734641544857475)
                ·
                  rfl

theorem cell20_626458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_626458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626458 prefixEnd_626458 := by exact prefixLift 626458
  have htrace : WordTrace (prefixWord ++ tailWord_626458) baseStart_626458 baseEnd_626458 := by
    simpa [prefixWord, tailWord_626458, baseEnd_626458] using wordTrace_append hprefix tailTrace_626458
  have hstable : (prefixWord ++ tailWord_626458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626458).length < 2 ^ (prefixWord ++ tailWord_626458).sum := by decide
  have hdescent : baseEnd_626458 < baseStart_626458 := by decide
  rcases family_descends (prefixWord ++ tailWord_626458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626468 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_626468 : Nat := 118140960795 + 626468 * 2 ^ 59
def prefixEnd_626468 : Nat := 4983230072969 + 3 ^ 40 * 626468 * 2
def baseEnd_626468 : Nat := 285937065476409044239051

theorem tailTrace_626468 : CollatzResearch.WordTrace tailWord_626468 prefixEnd_626468 285937065476409044239051 := by
  unfold tailWord_626468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424582547210451530712029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15232776729613935374282705 11424582547210451530712029)
  ·
    refine ⟨4284218455203919324017011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11424582547210451530712029 4284218455203919324017011)
    ·
      refine ⟨6426327682805878986025517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284218455203919324017011 6426327682805878986025517)
      ·
        refine ⟨2409872881052204619759569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6426327682805878986025517 2409872881052204619759569)
        ·
          refine ⟨1807404660789153464819677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2409872881052204619759569 1807404660789153464819677)
          ·
            refine ⟨677776747795932549307379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1807404660789153464819677 677776747795932549307379)
            ·
              refine ⟨1016665121693898823961069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677776747795932549307379 1016665121693898823961069)
              ·
                refine ⟨381249420635212058985401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016665121693898823961069 381249420635212058985401)
                ·
                  refine ⟨285937065476409044239051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381249420635212058985401 285937065476409044239051)
                  ·
                    rfl

theorem cell20_626468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_626468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626468 prefixEnd_626468 := by exact prefixLift 626468
  have htrace : WordTrace (prefixWord ++ tailWord_626468) baseStart_626468 baseEnd_626468 := by
    simpa [prefixWord, tailWord_626468, baseEnd_626468] using wordTrace_append hprefix tailTrace_626468
  have hstable : (prefixWord ++ tailWord_626468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626468).length < 2 ^ (prefixWord ++ tailWord_626468).sum := by decide
  have hdescent : baseEnd_626468 < baseStart_626468 := by decide
  rcases family_descends (prefixWord ++ tailWord_626468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626503 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 3]
def baseStart_626503 : Nat := 118140960795 + 626503 * 2 ^ 59
def prefixEnd_626503 : Nat := 4983230072969 + 3 ^ 40 * 626503 * 2
def baseEnd_626503 : Nat := 285953040430104478072241

theorem tailTrace_626503 : CollatzResearch.WordTrace tailWord_626503 prefixEnd_626503 285953040430104478072241 := by
  unfold tailWord_626503
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850441649294104038948163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15233627766196069359298775 22850441649294104038948163)
  ·
    refine ⟨34275662473941156058422245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22850441649294104038948163 34275662473941156058422245)
    ·
      refine ⟨6426686713863966760954171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34275662473941156058422245 6426686713863966760954171)
      ·
        refine ⟨9640030070795950141431257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426686713863966760954171 9640030070795950141431257)
        ·
          refine ⟨7230022553096962606073443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640030070795950141431257 7230022553096962606073443)
          ·
            refine ⟨10845033829645443909110165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7230022553096962606073443 10845033829645443909110165)
            ·
              refine ⟨508360960764630183239539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10845033829645443909110165 508360960764630183239539)
              ·
                refine ⟨762541441146945274859309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508360960764630183239539 762541441146945274859309)
                ·
                  refine ⟨285953040430104478072241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762541441146945274859309 285953040430104478072241)
                  ·
                    rfl

theorem cell20_626503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_626503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626503 prefixEnd_626503 := by exact prefixLift 626503
  have htrace : WordTrace (prefixWord ++ tailWord_626503) baseStart_626503 baseEnd_626503 := by
    simpa [prefixWord, tailWord_626503, baseEnd_626503] using wordTrace_append hprefix tailTrace_626503
  have hstable : (prefixWord ++ tailWord_626503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626503).length < 2 ^ (prefixWord ++ tailWord_626503).sum := by decide
  have hdescent : baseEnd_626503 < baseStart_626503 := by decide
  rcases family_descends (prefixWord ++ tailWord_626503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626558 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_626558 : Nat := 118140960795 + 626558 * 2 ^ 59
def prefixEnd_626558 : Nat := 4983230072969 + 3 ^ 40 * 626558 * 2
def baseEnd_626558 : Nat := 285978143928768731238683

theorem tailTrace_626558 : CollatzResearch.WordTrace tailWord_626558 prefixEnd_626558 285978143928768731238683 := by
  unfold tailWord_626558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856555958011856054025041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15234965109396565621466885 2856555958011856054025041)
  ·
    refine ⟨2142416968508892040518781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2856555958011856054025041 2142416968508892040518781)
    ·
      refine ⟨803406363190834515194543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2142416968508892040518781 803406363190834515194543)
      ·
        refine ⟨1205109544786251772791815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803406363190834515194543 1205109544786251772791815)
        ·
          refine ⟨1807664317179377659187723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205109544786251772791815 1807664317179377659187723)
          ·
            refine ⟨2711496475769066488781585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807664317179377659187723 2711496475769066488781585)
            ·
              refine ⟨2033622356826799866586189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711496475769066488781585 2033622356826799866586189)
              ·
                refine ⟨762608383810049949969821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2033622356826799866586189 762608383810049949969821)
                ·
                  refine ⟨285978143928768731238683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762608383810049949969821 285978143928768731238683)
                  ·
                    rfl

theorem cell20_626558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_626558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626558 prefixEnd_626558 := by exact prefixLift 626558
  have htrace : WordTrace (prefixWord ++ tailWord_626558) baseStart_626558 baseEnd_626558 := by
    simpa [prefixWord, tailWord_626558, baseEnd_626558] using wordTrace_append hprefix tailTrace_626558
  have hstable : (prefixWord ++ tailWord_626558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626558).length < 2 ^ (prefixWord ++ tailWord_626558).sum := by decide
  have hdescent : baseEnd_626558 < baseStart_626558 := by decide
  rcases family_descends (prefixWord ++ tailWord_626558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626569 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_626569 : Nat := 118140960795 + 626569 * 2 ^ 59
def prefixEnd_626569 : Nat := 4983230072969 + 3 ^ 40 * 626569 * 2
def baseEnd_626569 : Nat := 285983164628501581871971

theorem tailTrace_626569 : CollatzResearch.WordTrace tailWord_626569 prefixEnd_626569 285983164628501581871971 := by
  unfold tailWord_626569
  simp only [CollatzResearch.WordTrace]
  refine ⟨22852848867054997310850761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15235232578036664873900507 22852848867054997310850761)
  ·
    refine ⟨17139636650291247983138071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22852848867054997310850761 17139636650291247983138071)
    ·
      refine ⟨25709454975436871974707107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17139636650291247983138071 25709454975436871974707107)
      ·
        refine ⟨38564182463155307962060661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25709454975436871974707107 38564182463155307962060661)
        ·
          refine ⟨3615392105920810121443187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38564182463155307962060661 3615392105920810121443187)
          ·
            refine ⟨5423088158881215182164781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615392105920810121443187 5423088158881215182164781)
            ·
              refine ⟨2033658059580455693311793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5423088158881215182164781 2033658059580455693311793)
              ·
                refine ⟨1525243544685341769983845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033658059580455693311793 1525243544685341769983845)
                ·
                  refine ⟨285983164628501581871971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1525243544685341769983845 285983164628501581871971)
                  ·
                    rfl

theorem cell20_626569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_626569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626569 prefixEnd_626569 := by exact prefixLift 626569
  have htrace : WordTrace (prefixWord ++ tailWord_626569) baseStart_626569 baseEnd_626569 := by
    simpa [prefixWord, tailWord_626569, baseEnd_626569] using wordTrace_append hprefix tailTrace_626569
  have hstable : (prefixWord ++ tailWord_626569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626569).length < 2 ^ (prefixWord ++ tailWord_626569).sum := by decide
  have hdescent : baseEnd_626569 < baseStart_626569 := by decide
  rcases family_descends (prefixWord ++ tailWord_626569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626593 : List Nat := [1, 2, 3, 4, 2, 1, 7]
def baseStart_626593 : Nat := 118140960795 + 626593 * 2 ^ 59
def prefixEnd_626593 : Nat := 4983230072969 + 3 ^ 40 * 626593 * 2
def baseEnd_626593 : Nat := 31777124320273796119097

theorem tailTrace_626593 : CollatzResearch.WordTrace tailWord_626593 prefixEnd_626593 31777124320273796119097 := by
  unfold tailWord_626593
  simp only [CollatzResearch.WordTrace]
  refine ⟨22853724218968049409724433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15235816145978699606482955 22853724218968049409724433)
  ·
    refine ⟨17140293164226037057293325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22853724218968049409724433 17140293164226037057293325)
    ·
      refine ⟨6427609936584763896484997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17140293164226037057293325 6427609936584763896484997)
      ·
        refine ⟨1205176863109643230590937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6427609936584763896484997 1205176863109643230590937)
        ·
          refine ⟨903882647332232422943203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205176863109643230590937 903882647332232422943203)
          ·
            refine ⟨1355823970998348634414805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903882647332232422943203 1355823970998348634414805)
            ·
              refine ⟨31777124320273796119097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1355823970998348634414805 31777124320273796119097)
              ·
                rfl

theorem cell20_626593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_626593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626593 prefixEnd_626593 := by exact prefixLift 626593
  have htrace : WordTrace (prefixWord ++ tailWord_626593) baseStart_626593 baseEnd_626593 := by
    simpa [prefixWord, tailWord_626593, baseEnd_626593] using wordTrace_append hprefix tailTrace_626593
  have hstable : (prefixWord ++ tailWord_626593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626593).length < 2 ^ (prefixWord ++ tailWord_626593).sum := by decide
  have hdescent : baseEnd_626593 < baseStart_626593 := by decide
  rcases family_descends (prefixWord ++ tailWord_626593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626607 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_626607 : Nat := 118140960795 + 626607 * 2 ^ 59
def prefixEnd_626607 : Nat := 4983230072969 + 3 ^ 40 * 626607 * 2
def baseEnd_626607 : Nat := 286000508863942338605149

theorem tailTrace_626607 : CollatzResearch.WordTrace tailWord_626607 prefixEnd_626607 286000508863942338605149 := by
  unfold tailWord_626607
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854234840917329800734075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15236156560611553200489383 22854234840917329800734075)
  ·
    refine ⟨34281352261375994701101113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22854234840917329800734075 34281352261375994701101113)
    ·
      refine ⟨25711014196031996025825835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34281352261375994701101113 25711014196031996025825835)
      ·
        refine ⟨38566521294047994038738753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25711014196031996025825835 38566521294047994038738753)
        ·
          refine ⟨28924890970535995529054065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38566521294047994038738753 28924890970535995529054065)
          ·
            refine ⟨21693668227901996646790549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28924890970535995529054065 21693668227901996646790549)
            ·
              refine ⟨1016890698182906092818307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21693668227901996646790549 1016890698182906092818307)
              ·
                refine ⟨1525336047274359139227461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016890698182906092818307 1525336047274359139227461)
                ·
                  refine ⟨286000508863942338605149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1525336047274359139227461 286000508863942338605149)
                  ·
                    rfl

theorem cell20_626607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_626607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626607 prefixEnd_626607 := by exact prefixLift 626607
  have htrace : WordTrace (prefixWord ++ tailWord_626607) baseStart_626607 baseEnd_626607 := by
    simpa [prefixWord, tailWord_626607, baseEnd_626607] using wordTrace_append hprefix tailTrace_626607
  have hstable : (prefixWord ++ tailWord_626607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626607).length < 2 ^ (prefixWord ++ tailWord_626607).sum := by decide
  have hdescent : baseEnd_626607 < baseStart_626607 := by decide
  rcases family_descends (prefixWord ++ tailWord_626607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626617 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 3]
def baseStart_626617 : Nat := 118140960795 + 626617 * 2 ^ 59
def prefixEnd_626617 : Nat := 4983230072969 + 3 ^ 40 * 626617 * 2
def baseEnd_626617 : Nat := 286005073136426748271775

theorem tailTrace_626617 : CollatzResearch.WordTrace tailWord_626617 prefixEnd_626617 286005073136426748271775 := by
  unfold tailWord_626617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854599570881101508598105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15236399713920734339065403 22854599570881101508598105)
  ·
    refine ⟨17140949678160826131448579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22854599570881101508598105 17140949678160826131448579)
    ·
      refine ⟨25711424517241239197172869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17140949678160826131448579 25711424517241239197172869)
      ·
        refine ⟨4820892096982732349469913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25711424517241239197172869 4820892096982732349469913)
        ·
          refine ⟨3615669072737049262102435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4820892096982732349469913 3615669072737049262102435)
          ·
            refine ⟨5423503609105573893153653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615669072737049262102435 5423503609105573893153653)
            ·
              refine ⟨508453463353647552483155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5423503609105573893153653 508453463353647552483155)
              ·
                refine ⟨762680195030471328724733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508453463353647552483155 762680195030471328724733)
                ·
                  refine ⟨286005073136426748271775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762680195030471328724733 286005073136426748271775)
                  ·
                    rfl

theorem cell20_626617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_626617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626617 prefixEnd_626617 := by exact prefixLift 626617
  have htrace : WordTrace (prefixWord ++ tailWord_626617) baseStart_626617 baseEnd_626617 := by
    simpa [prefixWord, tailWord_626617, baseEnd_626617] using wordTrace_append hprefix tailTrace_626617
  have hstable : (prefixWord ++ tailWord_626617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626617).length < 2 ^ (prefixWord ++ tailWord_626617).sum := by decide
  have hdescent : baseEnd_626617 < baseStart_626617 := by decide
  rcases family_descends (prefixWord ++ tailWord_626617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626658 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_626658 : Nat := 118140960795 + 626658 * 2 ^ 59
def prefixEnd_626658 : Nat := 4983230072969 + 3 ^ 40 * 626658 * 2
def baseEnd_626658 : Nat := 286023786653612827904941

theorem tailTrace_626658 : CollatzResearch.WordTrace tailWord_626658 prefixEnd_626658 286023786653612827904941 := by
  unfold tailWord_626658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5714023740933141377710157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15237396642488377007227085 5714023740933141377710157)
  ·
    refine ⟨2142758902849928016641309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5714023740933141377710157 2142758902849928016641309)
    ·
      refine ⟨803534588568723006240491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2142758902849928016641309 803534588568723006240491)
      ·
        refine ⟨1205301882853084509360737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803534588568723006240491 1205301882853084509360737)
        ·
          refine ⟨903976412139813382020553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205301882853084509360737 903976412139813382020553)
          ·
            refine ⟨677982309104860036515415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903976412139813382020553 677982309104860036515415)
            ·
              refine ⟨1016973463657290054773123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677982309104860036515415 1016973463657290054773123)
              ·
                refine ⟨1525460195485935082159685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016973463657290054773123 1525460195485935082159685)
                ·
                  refine ⟨286023786653612827904941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1525460195485935082159685 286023786653612827904941)
                  ·
                    rfl

theorem cell20_626658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_626658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626658 prefixEnd_626658 := by exact prefixLift 626658
  have htrace : WordTrace (prefixWord ++ tailWord_626658) baseStart_626658 baseEnd_626658 := by
    simpa [prefixWord, tailWord_626658, baseEnd_626658] using wordTrace_append hprefix tailTrace_626658
  have hstable : (prefixWord ++ tailWord_626658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626658).length < 2 ^ (prefixWord ++ tailWord_626658).sum := by decide
  have hdescent : baseEnd_626658 < baseStart_626658 := by decide
  rcases family_descends (prefixWord ++ tailWord_626658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626700 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_626700 : Nat := 118140960795 + 626700 * 2 ^ 59
def prefixEnd_626700 : Nat := 4983230072969 + 3 ^ 40 * 626700 * 2
def baseEnd_626700 : Nat := 286042956598047348504769

theorem tailTrace_626700 : CollatzResearch.WordTrace tailWord_626700 prefixEnd_626700 286042956598047348504769 := by
  unfold tailWord_626700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428813414790203341934777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15238417886386937789246369 11428813414790203341934777)
  ·
    refine ⟨8571610061092652506451083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11428813414790203341934777 8571610061092652506451083)
    ·
      refine ⟨12857415091638978759676625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8571610061092652506451083 12857415091638978759676625)
      ·
        refine ⟨9643061318729234069757469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12857415091638978759676625 9643061318729234069757469)
        ·
          refine ⟨3616147994523462776159051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9643061318729234069757469 3616147994523462776159051)
          ·
            refine ⟨5424221991785194164238577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616147994523462776159051 5424221991785194164238577)
            ·
              refine ⟨4068166493838895623178933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5424221991785194164238577 4068166493838895623178933)
              ·
                refine ⟨381390608797396464673025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4068166493838895623178933 381390608797396464673025)
                ·
                  refine ⟨286042956598047348504769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381390608797396464673025 286042956598047348504769)
                  ·
                    rfl

theorem cell20_626700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_626700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626700 prefixEnd_626700 := by exact prefixLift 626700
  have htrace : WordTrace (prefixWord ++ tailWord_626700) baseStart_626700 baseEnd_626700 := by
    simpa [prefixWord, tailWord_626700, baseEnd_626700] using wordTrace_append hprefix tailTrace_626700
  have hstable : (prefixWord ++ tailWord_626700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626700).length < 2 ^ (prefixWord ++ tailWord_626700).sum := by decide
  have hdescent : baseEnd_626700 < baseStart_626700 := by decide
  rcases family_descends (prefixWord ++ tailWord_626700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626704 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_626704 : Nat := 118140960795 + 626704 * 2 ^ 59
def prefixEnd_626704 : Nat := 4983230072969 + 3 ^ 40 * 626704 * 2
def baseEnd_626704 : Nat := 286044782307041112371419

theorem tailTrace_626704 : CollatzResearch.WordTrace tailWord_626704 prefixEnd_626704 286044782307041112371419 := by
  unfold tailWord_626704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428886360782957683507583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15238515147710610244676777 11428886360782957683507583)
  ·
    refine ⟨17143329541174436525261375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11428886360782957683507583 17143329541174436525261375)
    ·
      refine ⟨25714994311761654787892063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17143329541174436525261375 25714994311761654787892063)
      ·
        refine ⟨38572491467642482181838095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25714994311761654787892063 38572491467642482181838095)
        ·
          refine ⟨57858737201463723272757143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38572491467642482181838095 57858737201463723272757143)
          ·
            refine ⟨86788105802195584909135715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57858737201463723272757143 86788105802195584909135715)
            ·
              refine ⟨130182158703293377363703573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86788105802195584909135715 130182158703293377363703573)
              ·
                refine ⟨6102288689216877063923605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130182158703293377363703573 6102288689216877063923605)
                ·
                  refine ⟨286044782307041112371419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6102288689216877063923605 286044782307041112371419)
                  ·
                    rfl

theorem cell20_626704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_626704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626704 prefixEnd_626704 := by exact prefixLift 626704
  have htrace : WordTrace (prefixWord ++ tailWord_626704) baseStart_626704 baseEnd_626704 := by
    simpa [prefixWord, tailWord_626704, baseEnd_626704] using wordTrace_append hprefix tailTrace_626704
  have hstable : (prefixWord ++ tailWord_626704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626704).length < 2 ^ (prefixWord ++ tailWord_626704).sum := by decide
  have hdescent : baseEnd_626704 < baseStart_626704 := by decide
  rcases family_descends (prefixWord ++ tailWord_626704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626714 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_626714 : Nat := 118140960795 + 626714 * 2 ^ 59
def prefixEnd_626714 : Nat := 4983230072969 + 3 ^ 40 * 626714 * 2
def baseEnd_626714 : Nat := 286049346579525522038045

theorem tailTrace_626714 : CollatzResearch.WordTrace tailWord_626714 prefixEnd_626714 286049346579525522038045 := by
  unfold tailWord_626714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5714534362882421768719799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15238758301019791383252797 5714534362882421768719799)
  ·
    refine ⟨8571801544323632653079699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5714534362882421768719799 8571801544323632653079699)
    ·
      refine ⟨12857702316485448979619549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8571801544323632653079699 12857702316485448979619549)
      ·
        refine ⟨4821638368682043367357331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12857702316485448979619549 4821638368682043367357331)
        ·
          refine ⟨7232457553023065051035997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821638368682043367357331 7232457553023065051035997)
          ·
            refine ⟨2712171582383649394138499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7232457553023065051035997 2712171582383649394138499)
            ·
              refine ⟨4068257373575474091207749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712171582383649394138499 4068257373575474091207749)
              ·
                refine ⟨762798257545401392101453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4068257373575474091207749 762798257545401392101453)
                ·
                  refine ⟨286049346579525522038045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762798257545401392101453 286049346579525522038045)
                  ·
                    rfl

theorem cell20_626714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_626714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626714 prefixEnd_626714 := by exact prefixLift 626714
  have htrace : WordTrace (prefixWord ++ tailWord_626714) baseStart_626714 baseEnd_626714 := by
    simpa [prefixWord, tailWord_626714, baseEnd_626714] using wordTrace_append hprefix tailTrace_626714
  have hstable : (prefixWord ++ tailWord_626714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626714).length < 2 ^ (prefixWord ++ tailWord_626714).sum := by decide
  have hdescent : baseEnd_626714 < baseStart_626714 := by decide
  rcases family_descends (prefixWord ++ tailWord_626714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626717 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 2]
def baseStart_626717 : Nat := 118140960795 + 626717 * 2 ^ 59
def prefixEnd_626717 : Nat := 4983230072969 + 3 ^ 40 * 626717 * 2
def baseEnd_626717 : Nat := 286050715861270844938033

theorem tailTrace_626717 : CollatzResearch.WordTrace tailWord_626717 prefixEnd_626717 286050715861270844938033 := by
  unfold tailWord_626717
  simp only [CollatzResearch.WordTrace]
  refine ⟨22858246870518818587238405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15238831247012545724825603 22858246870518818587238405)
  ·
    refine ⟨4285921288222278485107201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22858246870518818587238405 4285921288222278485107201)
    ·
      refine ⟨3214440966166708863830401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4285921288222278485107201 3214440966166708863830401)
      ·
        refine ⟨2410830724625031647872801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3214440966166708863830401 2410830724625031647872801)
        ·
          refine ⟨1808123043468773735904601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2410830724625031647872801 1808123043468773735904601)
          ·
            refine ⟨1356092282601580301928451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808123043468773735904601 1356092282601580301928451)
            ·
              refine ⟨2034138423902370452892677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356092282601580301928451 2034138423902370452892677)
              ·
                refine ⟨381400954481694459917377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034138423902370452892677 381400954481694459917377)
                ·
                  refine ⟨286050715861270844938033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381400954481694459917377 286050715861270844938033)
                  ·
                    rfl

theorem cell20_626717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_626717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626717 prefixEnd_626717 := by exact prefixLift 626717
  have htrace : WordTrace (prefixWord ++ tailWord_626717) baseStart_626717 baseEnd_626717 := by
    simpa [prefixWord, tailWord_626717, baseEnd_626717] using wordTrace_append hprefix tailTrace_626717
  have hstable : (prefixWord ++ tailWord_626717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626717).length < 2 ^ (prefixWord ++ tailWord_626717).sum := by decide
  have hdescent : baseEnd_626717 < baseStart_626717 := by decide
  rcases family_descends (prefixWord ++ tailWord_626717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626724 : List Nat := [2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_626724 : Nat := 118140960795 + 626724 * 2 ^ 59
def prefixEnd_626724 : Nat := 4983230072969 + 3 ^ 40 * 626724 * 2
def baseEnd_626724 : Nat := 95351303617336643901557

theorem tailTrace_626724 : CollatzResearch.WordTrace tailWord_626724 prefixEnd_626724 95351303617336643901557 := by
  unfold tailWord_626724
  simp only [CollatzResearch.WordTrace]
  refine ⟨11429251090746729391371613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15239001454328972521828817 11429251090746729391371613)
  ·
    refine ⟨4285969159030023521764355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11429251090746729391371613 4285969159030023521764355)
    ·
      refine ⟨6428953738545035282646533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285969159030023521764355 6428953738545035282646533)
      ·
        refine ⟨1205428825977194115496225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6428953738545035282646533 1205428825977194115496225)
        ·
          refine ⟨904071619482895586622169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205428825977194115496225 904071619482895586622169)
          ·
            refine ⟨678053714612171689966627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904071619482895586622169 678053714612171689966627)
            ·
              refine ⟨1017080571918257534949941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678053714612171689966627 1017080571918257534949941)
              ·
                refine ⟨95351303617336643901557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1017080571918257534949941 95351303617336643901557)
                ·
                  rfl

theorem cell20_626724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_626724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626724 prefixEnd_626724 := by exact prefixLift 626724
  have htrace : WordTrace (prefixWord ++ tailWord_626724) baseStart_626724 baseEnd_626724 := by
    simpa [prefixWord, tailWord_626724, baseEnd_626724] using wordTrace_append hprefix tailTrace_626724
  have hstable : (prefixWord ++ tailWord_626724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626724).length < 2 ^ (prefixWord ++ tailWord_626724).sum := by decide
  have hdescent : baseEnd_626724 < baseStart_626724 := by decide
  rcases family_descends (prefixWord ++ tailWord_626724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626766 : List Nat := [4, 1, 1, 1, 1, 5, 7]
def baseStart_626766 : Nat := 118140960795 + 626766 * 2 ^ 59
def prefixEnd_626766 : Nat := 4983230072969 + 3 ^ 40 * 626766 * 2
def baseEnd_626766 : Nat := 31785897866271605811611

theorem tailTrace_626766 : CollatzResearch.WordTrace tailWord_626766 prefixEnd_626766 31785897866271605811611 := by
  unfold tailWord_626766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857504255917662494471519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15240022698227533303848101 2857504255917662494471519)
  ·
    refine ⟨4286256383876493741707279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2857504255917662494471519 4286256383876493741707279)
    ·
      refine ⟨6429384575814740612560919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286256383876493741707279 6429384575814740612560919)
      ·
        refine ⟨9644076863722110918841379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6429384575814740612560919 9644076863722110918841379)
        ·
          refine ⟨14466115295583166378262069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644076863722110918841379 14466115295583166378262069)
          ·
            refine ⟨1356198308960921847962069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14466115295583166378262069 1356198308960921847962069)
            ·
              refine ⟨31785897866271605811611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1356198308960921847962069 31785897866271605811611)
              ·
                rfl

theorem cell20_626766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_626766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626766 prefixEnd_626766 := by exact prefixLift 626766
  have htrace : WordTrace (prefixWord ++ tailWord_626766) baseStart_626766 baseEnd_626766 := by
    simpa [prefixWord, tailWord_626766, baseEnd_626766] using wordTrace_append hprefix tailTrace_626766
  have hstable : (prefixWord ++ tailWord_626766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626766).length < 2 ^ (prefixWord ++ tailWord_626766).sum := by decide
  have hdescent : baseEnd_626766 < baseStart_626766 := by decide
  rcases family_descends (prefixWord ++ tailWord_626766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626776 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_626776 : Nat := 118140960795 + 626776 * 2 ^ 59
def prefixEnd_626776 : Nat := 4983230072969 + 3 ^ 40 * 626776 * 2
def baseEnd_626776 : Nat := 286077645068928861971125

theorem tailTrace_626776 : CollatzResearch.WordTrace tailWord_626776 prefixEnd_626776 286077645068928861971125 := by
  unfold tailWord_626776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11430199388652535831818091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15240265851536714442424121 11430199388652535831818091)
  ·
    refine ⟨17145299082978803747727137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11430199388652535831818091 17145299082978803747727137)
    ·
      refine ⟨12858974312234102810795353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17145299082978803747727137 12858974312234102810795353)
      ·
        refine ⟨9644230734175577108096515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12858974312234102810795353 9644230734175577108096515)
        ·
          refine ⟨14466346101263365662144773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644230734175577108096515 14466346101263365662144773)
          ·
            refine ⟨2712439893986881061652145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14466346101263365662144773 2712439893986881061652145)
            ·
              refine ⟨2034329920490160796239109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712439893986881061652145 2034329920490160796239109)
              ·
                refine ⟨381436860091905149294833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034329920490160796239109 381436860091905149294833)
                ·
                  refine ⟨286077645068928861971125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381436860091905149294833 286077645068928861971125)
                  ·
                    rfl

theorem cell20_626776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_626776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626776 prefixEnd_626776 := by exact prefixLift 626776
  have htrace : WordTrace (prefixWord ++ tailWord_626776) baseStart_626776 baseEnd_626776 := by
    simpa [prefixWord, tailWord_626776, baseEnd_626776] using wordTrace_append hprefix tailTrace_626776
  have hstable : (prefixWord ++ tailWord_626776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626776).length < 2 ^ (prefixWord ++ tailWord_626776).sum := by decide
  have hdescent : baseEnd_626776 < baseStart_626776 := by decide
  rcases family_descends (prefixWord ++ tailWord_626776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626782 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_626782 : Nat := 118140960795 + 626782 * 2 ^ 59
def prefixEnd_626782 : Nat := 4983230072969 + 3 ^ 40 * 626782 * 2
def baseEnd_626782 : Nat := 286080383632419507771101

theorem tailTrace_626782 : CollatzResearch.WordTrace tailWord_626782 prefixEnd_626782 286080383632419507771101 := by
  unfold tailWord_626782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857577201910416836044325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15240411743522223125569733 2857577201910416836044325)
  ·
    refine ⟨535795725358203156758311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2857577201910416836044325 535795725358203156758311)
    ·
      refine ⟨803693588037304735137467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535795725358203156758311 803693588037304735137467)
      ·
        refine ⟨1205540382055957102706201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803693588037304735137467 1205540382055957102706201)
        ·
          refine ⟨904155286541967827029651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205540382055957102706201 904155286541967827029651)
          ·
            refine ⟨1356232929812951740544477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904155286541967827029651 1356232929812951740544477)
            ·
              refine ⟨508587348679856902704179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1356232929812951740544477 508587348679856902704179)
              ·
                refine ⟨762881023019785354056269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508587348679856902704179 762881023019785354056269)
                ·
                  refine ⟨286080383632419507771101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762881023019785354056269 286080383632419507771101)
                  ·
                    rfl

theorem cell20_626782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_626782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626782 prefixEnd_626782 := by exact prefixLift 626782
  have htrace : WordTrace (prefixWord ++ tailWord_626782) baseStart_626782 baseEnd_626782 := by
    simpa [prefixWord, tailWord_626782, baseEnd_626782] using wordTrace_append hprefix tailTrace_626782
  have hstable : (prefixWord ++ tailWord_626782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626782).length < 2 ^ (prefixWord ++ tailWord_626782).sum := by decide
  have hdescent : baseEnd_626782 < baseStart_626782 := by decide
  rcases family_descends (prefixWord ++ tailWord_626782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626797 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_626797 : Nat := 118140960795 + 626797 * 2 ^ 59
def prefixEnd_626797 : Nat := 4983230072969 + 3 ^ 40 * 626797 * 2
def baseEnd_626797 : Nat := 286087230041146122271039

theorem tailTrace_626797 : CollatzResearch.WordTrace tailWord_626797 prefixEnd_626797 286087230041146122271039 := by
  unfold tailWord_626797
  simp only [CollatzResearch.WordTrace]
  refine ⟨22861164710228992250150645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15240776473485994833433763 22861164710228992250150645)
  ·
    refine ⟨2143234191583968023451623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22861164710228992250150645 2143234191583968023451623)
    ·
      refine ⟨3214851287375952035177435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143234191583968023451623 3214851287375952035177435)
      ·
        refine ⟨4822276931063928052766153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214851287375952035177435 4822276931063928052766153)
        ·
          refine ⟨3616707698297946039574615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4822276931063928052766153 3616707698297946039574615)
          ·
            refine ⟨5425061547446919059361923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616707698297946039574615 5425061547446919059361923)
            ·
              refine ⟨8137592321170378589042885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425061547446919059361923 8137592321170378589042885)
              ·
                refine ⟨1525798560219445985445541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8137592321170378589042885 1525798560219445985445541)
                ·
                  refine ⟨286087230041146122271039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1525798560219445985445541 286087230041146122271039)
                  ·
                    rfl

theorem cell20_626797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_626797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626797 prefixEnd_626797 := by exact prefixLift 626797
  have htrace : WordTrace (prefixWord ++ tailWord_626797) baseStart_626797 baseEnd_626797 := by
    simpa [prefixWord, tailWord_626797, baseEnd_626797] using wordTrace_append hprefix tailTrace_626797
  have hstable : (prefixWord ++ tailWord_626797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626797).length < 2 ^ (prefixWord ++ tailWord_626797).sum := by decide
  have hdescent : baseEnd_626797 < baseStart_626797 := by decide
  rcases family_descends (prefixWord ++ tailWord_626797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626845 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 3]
def baseStart_626845 : Nat := 118140960795 + 626845 * 2 ^ 59
def prefixEnd_626845 : Nat := 4983230072969 + 3 ^ 40 * 626845 * 2
def baseEnd_626845 : Nat := 286109138549071288670843

theorem tailTrace_626845 : CollatzResearch.WordTrace tailWord_626845 prefixEnd_626845 286109138549071288670843 := by
  unfold tailWord_626845
  simp only [CollatzResearch.WordTrace]
  refine ⟨22862915414055096447897989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15241943609370064298598659 22862915414055096447897989)
  ·
    refine ⟨4286796640135330583980873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22862915414055096447897989 4286796640135330583980873)
    ·
      refine ⟨3215097480101497937985655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4286796640135330583980873 3215097480101497937985655)
      ·
        refine ⟨4822646220152246906978483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215097480101497937985655 4822646220152246906978483)
        ·
          refine ⟨7233969330228370360467725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4822646220152246906978483 7233969330228370360467725)
          ·
            refine ⟨2712738498835638885175397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7233969330228370360467725 2712738498835638885175397)
            ·
              refine ⟨508638468531682290970387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2712738498835638885175397 508638468531682290970387)
              ·
                refine ⟨762957702797523436455581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508638468531682290970387 762957702797523436455581)
                ·
                  refine ⟨286109138549071288670843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762957702797523436455581 286109138549071288670843)
                  ·
                    rfl

theorem cell20_626845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_626845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626845 prefixEnd_626845 := by exact prefixLift 626845
  have htrace : WordTrace (prefixWord ++ tailWord_626845) baseStart_626845 baseEnd_626845 := by
    simpa [prefixWord, tailWord_626845, baseEnd_626845] using wordTrace_append hprefix tailTrace_626845
  have hstable : (prefixWord ++ tailWord_626845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626845).length < 2 ^ (prefixWord ++ tailWord_626845).sum := by decide
  have hdescent : baseEnd_626845 < baseStart_626845 := by decide
  rcases family_descends (prefixWord ++ tailWord_626845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626882 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_626882 : Nat := 118140960795 + 626882 * 2 ^ 59
def prefixEnd_626882 : Nat := 4983230072969 + 3 ^ 40 * 626882 * 2
def baseEnd_626882 : Nat := 286126026357263604437359

theorem tailTrace_626882 : CollatzResearch.WordTrace tailWord_626882 prefixEnd_626882 286126026357263604437359 := by
  unfold tailWord_626882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716066228730262941748725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15242843276614034511329933 5716066228730262941748725)
  ·
    refine ⟨535881208943462150788943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5716066228730262941748725 535881208943462150788943)
    ·
      refine ⟨803821813415193226183415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535881208943462150788943 803821813415193226183415)
      ·
        refine ⟨1205732720122789839275123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803821813415193226183415 1205732720122789839275123)
        ·
          refine ⟨1808599080184184758912685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205732720122789839275123 1808599080184184758912685)
          ·
            refine ⟨678224655069069284592257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1808599080184184758912685 678224655069069284592257)
            ·
              refine ⟨508668491301801963444193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678224655069069284592257 508668491301801963444193)
              ·
                refine ⟨381501368476351472583145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508668491301801963444193 381501368476351472583145)
                ·
                  refine ⟨286126026357263604437359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381501368476351472583145 286126026357263604437359)
                  ·
                    rfl

theorem cell20_626882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_626882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626882 prefixEnd_626882 := by exact prefixLift 626882
  have htrace : WordTrace (prefixWord ++ tailWord_626882) baseStart_626882 baseEnd_626882 := by
    simpa [prefixWord, tailWord_626882, baseEnd_626882] using wordTrace_append hprefix tailTrace_626882
  have hstable : (prefixWord ++ tailWord_626882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626882).length < 2 ^ (prefixWord ++ tailWord_626882).sum := by decide
  have hdescent : baseEnd_626882 < baseStart_626882 := by decide
  rcases family_descends (prefixWord ++ tailWord_626882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626890 : List Nat := [3, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_626890 : Nat := 118140960795 + 626890 * 2 ^ 59
def prefixEnd_626890 : Nat := 4983230072969 + 3 ^ 40 * 626890 * 2
def baseEnd_626890 : Nat := 286129677775251132170659

theorem tailTrace_626890 : CollatzResearch.WordTrace tailWord_626890 prefixEnd_626890 286129677775251132170659 := by
  unfold tailWord_626890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716139174723017283321531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15243037799261379422190749 5716139174723017283321531)
  ·
    refine ⟨8574208762084525924982297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5716139174723017283321531 8574208762084525924982297)
    ·
      refine ⟨6430656571563394443736723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8574208762084525924982297 6430656571563394443736723)
      ·
        refine ⟨9645984857345091665605085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6430656571563394443736723 9645984857345091665605085)
        ·
          refine ⟨3617244321504409374601907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9645984857345091665605085 3617244321504409374601907)
          ·
            refine ⟨5425866482256614061902861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617244321504409374601907 5425866482256614061902861)
            ·
              refine ⟨2034699930846230273213573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5425866482256614061902861 2034699930846230273213573)
              ·
                refine ⟨381506237033668176227545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034699930846230273213573 381506237033668176227545)
                ·
                  refine ⟨286129677775251132170659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381506237033668176227545 286129677775251132170659)
                  ·
                    rfl

theorem cell20_626890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_626890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626890 prefixEnd_626890 := by exact prefixLift 626890
  have htrace : WordTrace (prefixWord ++ tailWord_626890) baseStart_626890 baseEnd_626890 := by
    simpa [prefixWord, tailWord_626890, baseEnd_626890] using wordTrace_append hprefix tailTrace_626890
  have hstable : (prefixWord ++ tailWord_626890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626890).length < 2 ^ (prefixWord ++ tailWord_626890).sum := by decide
  have hdescent : baseEnd_626890 < baseStart_626890 := by decide
  rcases family_descends (prefixWord ++ tailWord_626890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626904 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_626904 : Nat := 118140960795 + 626904 * 2 ^ 59
def prefixEnd_626904 : Nat := 4983230072969 + 3 ^ 40 * 626904 * 2
def baseEnd_626904 : Nat := 286136067756729305703935

theorem tailTrace_626904 : CollatzResearch.WordTrace tailWord_626904 prefixEnd_626904 286136067756729305703935 := by
  unfold tailWord_626904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11432533660420674762147883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15243378213894233016197177 11432533660420674762147883)
  ·
    refine ⟨17148800490631012143221825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11432533660420674762147883 17148800490631012143221825)
    ·
      refine ⟨12861600367973259107416369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17148800490631012143221825 12861600367973259107416369)
      ·
        refine ⟨9646200275979944330562277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12861600367973259107416369 9646200275979944330562277)
        ·
          refine ⟨1808662551746239561980427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9646200275979944330562277 1808662551746239561980427)
          ·
            refine ⟨2712993827619359342970641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808662551746239561980427 2712993827619359342970641)
            ·
              refine ⟨2034745370714519507227981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712993827619359342970641 2034745370714519507227981)
              ·
                refine ⟨763029514017944815210493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034745370714519507227981 763029514017944815210493)
                ·
                  refine ⟨286136067756729305703935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763029514017944815210493 286136067756729305703935)
                  ·
                    rfl

theorem cell20_626904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_626904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626904 prefixEnd_626904 := by exact prefixLift 626904
  have htrace : WordTrace (prefixWord ++ tailWord_626904) baseStart_626904 baseEnd_626904 := by
    simpa [prefixWord, tailWord_626904, baseEnd_626904] using wordTrace_append hprefix tailTrace_626904
  have hstable : (prefixWord ++ tailWord_626904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626904).length < 2 ^ (prefixWord ++ tailWord_626904).sum := by decide
  have hdescent : baseEnd_626904 < baseStart_626904 := by decide
  rcases family_descends (prefixWord ++ tailWord_626904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626942 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_626942 : Nat := 118140960795 + 626942 * 2 ^ 59
def prefixEnd_626942 : Nat := 4983230072969 + 3 ^ 40 * 626942 * 2
def baseEnd_626942 : Nat := 286153411992170062437113

theorem tailTrace_626942 : CollatzResearch.WordTrace tailWord_626942 prefixEnd_626942 286153411992170062437113 := by
  unfold tailWord_626942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858306661837960251772385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15244302196469121342786053 2858306661837960251772385)
  ·
    refine ⟨2143729996378470188829289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2858306661837960251772385 2143729996378470188829289)
    ·
      refine ⟨1607797497283852641621967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143729996378470188829289 1607797497283852641621967)
      ·
        refine ⟨2411696245925778962432951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607797497283852641621967 2411696245925778962432951)
        ·
          refine ⟨3617544368888668443649427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411696245925778962432951 3617544368888668443649427)
          ·
            refine ⟨5426316553333002665474141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617544368888668443649427 5426316553333002665474141)
            ·
              refine ⟨2034868707499875999552803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5426316553333002665474141 2034868707499875999552803)
              ·
                refine ⟨3052303061249813999329205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034868707499875999552803 3052303061249813999329205)
                ·
                  refine ⟨286153411992170062437113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3052303061249813999329205 286153411992170062437113)
                  ·
                    rfl

theorem cell20_626942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_626942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626942 prefixEnd_626942 := by exact prefixLift 626942
  have htrace : WordTrace (prefixWord ++ tailWord_626942) baseStart_626942 baseEnd_626942 := by
    simpa [prefixWord, tailWord_626942, baseEnd_626942] using wordTrace_append hprefix tailTrace_626942
  have hstable : (prefixWord ++ tailWord_626942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626942).length < 2 ^ (prefixWord ++ tailWord_626942).sum := by decide
  have hdescent : baseEnd_626942 < baseStart_626942 := by decide
  rcases family_descends (prefixWord ++ tailWord_626942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626963 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_626963 : Nat := 118140960795 + 626963 * 2 ^ 59
def prefixEnd_626963 : Nat := 4983230072969 + 3 ^ 40 * 626963 * 2
def baseEnd_626963 : Nat := 286162996964387322737027

theorem tailTrace_626963 : CollatzResearch.WordTrace tailWord_626963 prefixEnd_626963 286162996964387322737027 := by
  unfold tailWord_626963
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867219227627602600693543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15244812818418401733795695 22867219227627602600693543)
  ·
    refine ⟨34300828841441403901040315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22867219227627602600693543 34300828841441403901040315)
    ·
      refine ⟨51451243262162105851560473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34300828841441403901040315 51451243262162105851560473)
      ·
        refine ⟨38588432446621579388670355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51451243262162105851560473 38588432446621579388670355)
        ·
          refine ⟨57882648669932369083005533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38588432446621579388670355 57882648669932369083005533)
          ·
            refine ⟨21705993251224638406127075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57882648669932369083005533 21705993251224638406127075)
            ·
              refine ⟨32558989876836957609190613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21705993251224638406127075 32558989876836957609190613)
              ·
                refine ⟨763101325238366193965405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32558989876836957609190613 763101325238366193965405)
                ·
                  refine ⟨286162996964387322737027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763101325238366193965405 286162996964387322737027)
                  ·
                    rfl

theorem cell20_626963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_626963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626963 prefixEnd_626963 := by exact prefixLift 626963
  have htrace : WordTrace (prefixWord ++ tailWord_626963) baseStart_626963 baseEnd_626963 := by
    simpa [prefixWord, tailWord_626963, baseEnd_626963] using wordTrace_append hprefix tailTrace_626963
  have hstable : (prefixWord ++ tailWord_626963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626963).length < 2 ^ (prefixWord ++ tailWord_626963).sum := by decide
  have hdescent : baseEnd_626963 < baseStart_626963 := by decide
  rcases family_descends (prefixWord ++ tailWord_626963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626973 : List Nat := [1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_626973 : Nat := 118140960795 + 626973 * 2 ^ 59
def prefixEnd_626973 : Nat := 4983230072969 + 3 ^ 40 * 626973 * 2
def baseEnd_626973 : Nat := 95389187078957244134551

theorem tailTrace_626973 : CollatzResearch.WordTrace tailWord_626973 prefixEnd_626973 95389187078957244134551 := by
  unfold tailWord_626973
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867583957591374308557573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15245055971727582872371715 22867583957591374308557573)
  ·
    refine ⟨4287671992048382682854545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22867583957591374308557573 4287671992048382682854545)
    ·
      refine ⟨3215753994036287012140909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4287671992048382682854545 3215753994036287012140909)
      ·
        refine ⟨1205907747763607629552841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3215753994036287012140909 1205907747763607629552841)
        ·
          refine ⟨904430810822705722164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205907747763607629552841 904430810822705722164631)
          ·
            refine ⟨1356646216234058583246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904430810822705722164631 1356646216234058583246947)
            ·
              refine ⟨2034969324351087874870421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356646216234058583246947 2034969324351087874870421)
              ·
                refine ⟨95389187078957244134551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034969324351087874870421 95389187078957244134551)
                ·
                  rfl

theorem cell20_626973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_626973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626973 prefixEnd_626973 := by exact prefixLift 626973
  have htrace : WordTrace (prefixWord ++ tailWord_626973) baseStart_626973 baseEnd_626973 := by
    simpa [prefixWord, tailWord_626973, baseEnd_626973] using wordTrace_append hprefix tailTrace_626973
  have hstable : (prefixWord ++ tailWord_626973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626973).length < 2 ^ (prefixWord ++ tailWord_626973).sum := by decide
  have hdescent : baseEnd_626973 < baseStart_626973 := by decide
  rcases family_descends (prefixWord ++ tailWord_626973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626990 : List Nat := [4, 1, 3, 3, 1, 2, 6]
def baseStart_626990 : Nat := 118140960795 + 626990 * 2 ^ 59
def prefixEnd_626990 : Nat := 4983230072969 + 3 ^ 40 * 626990 * 2
def baseEnd_626990 : Nat := 31797257833343914315213

theorem tailTrace_626990 : CollatzResearch.WordTrace tailWord_626990 prefixEnd_626990 31797257833343914315213 := by
  unfold tailWord_626990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858525499816223276490803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15245469332353190807950949 2858525499816223276490803)
  ·
    refine ⟨4287788249724334914736205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2858525499816223276490803 4287788249724334914736205)
    ·
      refine ⟨1607920593646625593026077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4287788249724334914736205 1607920593646625593026077)
      ·
        refine ⟨602970222617484597384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1607920593646625593026077 602970222617484597384779)
        ·
          refine ⟨904455333926226896077169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602970222617484597384779 904455333926226896077169)
          ·
            refine ⟨678341500444670172057877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904455333926226896077169 678341500444670172057877)
            ·
              refine ⟨31797257833343914315213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 678341500444670172057877 31797257833343914315213)
              ·
                rfl

theorem cell20_626990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_626990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626990 prefixEnd_626990 := by exact prefixLift 626990
  have htrace : WordTrace (prefixWord ++ tailWord_626990) baseStart_626990 baseEnd_626990 := by
    simpa [prefixWord, tailWord_626990, baseEnd_626990] using wordTrace_append hprefix tailTrace_626990
  have hstable : (prefixWord ++ tailWord_626990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626990).length < 2 ^ (prefixWord ++ tailWord_626990).sum := by decide
  have hdescent : baseEnd_626990 < baseStart_626990 := by decide
  rcases family_descends (prefixWord ++ tailWord_626990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627008 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_627008 : Nat := 118140960795 + 627008 * 2 ^ 59
def prefixEnd_627008 : Nat := 4983230072969 + 3 ^ 40 * 627008 * 2
def baseEnd_627008 : Nat := 286183536190567166236843

theorem tailTrace_627008 : CollatzResearch.WordTrace tailWord_627008 prefixEnd_627008 286183536190567166236843 := by
  unfold tailWord_627008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434430256232287643040839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15245907008309716857387785 11434430256232287643040839)
  ·
    refine ⟨17151645384348431464561259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11434430256232287643040839 17151645384348431464561259)
    ·
      refine ⟨25727468076522647196841889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17151645384348431464561259 25727468076522647196841889)
      ·
        refine ⟨19295601057391985397631417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25727468076522647196841889 19295601057391985397631417)
        ·
          refine ⟨14471700793043989048223563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19295601057391985397631417 14471700793043989048223563)
          ·
            refine ⟨21707551189565983572335345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14471700793043989048223563 21707551189565983572335345)
            ·
              refine ⟨16280663392174487679251509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21707551189565983572335345 16280663392174487679251509)
              ·
                refine ⟨1526312193016358219929829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16280663392174487679251509 1526312193016358219929829)
                ·
                  refine ⟨286183536190567166236843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526312193016358219929829 286183536190567166236843)
                  ·
                    rfl

theorem cell20_627008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_627008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627008 prefixEnd_627008 := by exact prefixLift 627008
  have htrace : WordTrace (prefixWord ++ tailWord_627008) baseStart_627008 baseEnd_627008 := by
    simpa [prefixWord, tailWord_627008, baseEnd_627008] using wordTrace_append hprefix tailTrace_627008
  have hstable : (prefixWord ++ tailWord_627008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627008).length < 2 ^ (prefixWord ++ tailWord_627008).sum := by decide
  have hdescent : baseEnd_627008 < baseStart_627008 := by decide
  rcases family_descends (prefixWord ++ tailWord_627008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627056 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_627056 : Nat := 118140960795 + 627056 * 2 ^ 59
def prefixEnd_627056 : Nat := 4983230072969 + 3 ^ 40 * 627056 * 2
def baseEnd_627056 : Nat := 286205444698492332636647

theorem tailTrace_627056 : CollatzResearch.WordTrace tailWord_627056 prefixEnd_627056 286205444698492332636647 := by
  unfold tailWord_627056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435305608145339741914511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15247074144193786322552681 11435305608145339741914511)
  ·
    refine ⟨17152958412218009612871767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11435305608145339741914511 17152958412218009612871767)
    ·
      refine ⟨25729437618327014419307651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17152958412218009612871767 25729437618327014419307651)
      ·
        refine ⟨38594156427490521628961477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25729437618327014419307651 38594156427490521628961477)
        ·
          refine ⟨7236404330154472805430277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38594156427490521628961477 7236404330154472805430277)
          ·
            refine ⟨1356825811903963651018177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7236404330154472805430277 1356825811903963651018177)
            ·
              refine ⟨1017619358927972738263633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356825811903963651018177 1017619358927972738263633)
              ·
                refine ⟨763214519195979553697725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017619358927972738263633 763214519195979553697725)
                ·
                  refine ⟨286205444698492332636647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763214519195979553697725 286205444698492332636647)
                  ·
                    rfl

theorem cell20_627056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_627056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627056 prefixEnd_627056 := by exact prefixLift 627056
  have htrace : WordTrace (prefixWord ++ tailWord_627056) baseStart_627056 baseEnd_627056 := by
    simpa [prefixWord, tailWord_627056, baseEnd_627056] using wordTrace_append hprefix tailTrace_627056
  have hstable : (prefixWord ++ tailWord_627056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627056).length < 2 ^ (prefixWord ++ tailWord_627056).sum := by decide
  have hdescent : baseEnd_627056 < baseStart_627056 := by decide
  rcases family_descends (prefixWord ++ tailWord_627056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627084 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_627084 : Nat := 118140960795 + 627084 * 2 ^ 59
def prefixEnd_627084 : Nat := 4983230072969 + 3 ^ 40 * 627084 * 2
def baseEnd_627084 : Nat := 286218224661448679703199

theorem tailTrace_627084 : CollatzResearch.WordTrace tailWord_627084 prefixEnd_627084 286218224661448679703199 := by
  unfold tailWord_627084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435816230094620132924153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15247754973459493510565537 11435816230094620132924153)
  ·
    refine ⟨8576862172570965099693115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11435816230094620132924153 8576862172570965099693115)
    ·
      refine ⟨12865293258856447649539673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8576862172570965099693115 12865293258856447649539673)
      ·
        refine ⟨9648969944142335737154755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12865293258856447649539673 9648969944142335737154755)
        ·
          refine ⟨14473454916213503605732133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648969944142335737154755 14473454916213503605732133)
          ·
            refine ⟨2713772796790031926074775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14473454916213503605732133 2713772796790031926074775)
            ·
              refine ⟨4070659195185047889112163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713772796790031926074775 4070659195185047889112163)
              ·
                refine ⟨6105988792777571833668245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070659195185047889112163 6105988792777571833668245)
                ·
                  refine ⟨286218224661448679703199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6105988792777571833668245 286218224661448679703199)
                  ·
                    rfl

theorem cell20_627084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_627084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627084 prefixEnd_627084 := by exact prefixLift 627084
  have htrace : WordTrace (prefixWord ++ tailWord_627084) baseStart_627084 baseEnd_627084 := by
    simpa [prefixWord, tailWord_627084, baseEnd_627084] using wordTrace_append hprefix tailTrace_627084
  have hstable : (prefixWord ++ tailWord_627084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627084).length < 2 ^ (prefixWord ++ tailWord_627084).sum := by decide
  have hdescent : baseEnd_627084 < baseStart_627084 := by decide
  rcases family_descends (prefixWord ++ tailWord_627084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627111 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_627111 : Nat := 118140960795 + 627111 * 2 ^ 59
def prefixEnd_627111 : Nat := 4983230072969 + 3 ^ 40 * 627111 * 2
def baseEnd_627111 : Nat := 286230548197156585803089

theorem tailTrace_627111 : CollatzResearch.WordTrace tailWord_627111 prefixEnd_627111 286230548197156585803089 := by
  unfold tailWord_627111
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872617231091423877081187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15248411487394282584720791 22872617231091423877081187)
  ·
    refine ⟨34308925846637135815621781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22872617231091423877081187 34308925846637135815621781)
    ·
      refine ⟨1608230899061115741357271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34308925846637135815621781 1608230899061115741357271)
      ·
        refine ⟨2412346348591673612035907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608230899061115741357271 2412346348591673612035907)
        ·
          refine ⟨3618519522887510418053861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412346348591673612035907 3618519522887510418053861)
          ·
            refine ⟨678472410541408203385099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3618519522887510418053861 678472410541408203385099)
            ·
              refine ⟨1017708615812112305077649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678472410541408203385099 1017708615812112305077649)
              ·
                refine ⟨763281461859084228808237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017708615812112305077649 763281461859084228808237)
                ·
                  refine ⟨286230548197156585803089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763281461859084228808237 286230548197156585803089)
                  ·
                    rfl

theorem cell20_627111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_627111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627111 prefixEnd_627111 := by exact prefixLift 627111
  have htrace : WordTrace (prefixWord ++ tailWord_627111) baseStart_627111 baseEnd_627111 := by
    simpa [prefixWord, tailWord_627111, baseEnd_627111] using wordTrace_append hprefix tailTrace_627111
  have hstable : (prefixWord ++ tailWord_627111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627111).length < 2 ^ (prefixWord ++ tailWord_627111).sum := by decide
  have hdescent : baseEnd_627111 < baseStart_627111 := by decide
  rcases family_descends (prefixWord ++ tailWord_627111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627114 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_627114 : Nat := 118140960795 + 627114 * 2 ^ 59
def prefixEnd_627114 : Nat := 4983230072969 + 3 ^ 40 * 627114 * 2
def baseEnd_627114 : Nat := 286231917478901908703077

theorem tailTrace_627114 : CollatzResearch.WordTrace tailWord_627114 prefixEnd_627114 286231917478901908703077 := by
  unfold tailWord_627114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5718181662520138847360099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15248484433387036926293597 5718181662520138847360099)
  ·
    refine ⟨8577272493780208271040149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5718181662520138847360099 8577272493780208271040149)
    ·
      refine ⟨402059648145947262705007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8577272493780208271040149 402059648145947262705007)
      ·
        refine ⟨603089472218920894057511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402059648145947262705007 603089472218920894057511)
        ·
          refine ⟨904634208328381341086267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603089472218920894057511 904634208328381341086267)
          ·
            refine ⟨1356951312492572011629401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904634208328381341086267 1356951312492572011629401)
            ·
              refine ⟨1017713484369429008722051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356951312492572011629401 1017713484369429008722051)
              ·
                refine ⟨1526570226554143513083077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017713484369429008722051 1526570226554143513083077)
                ·
                  refine ⟨286231917478901908703077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526570226554143513083077 286231917478901908703077)
                  ·
                    rfl

theorem cell20_627114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_627114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627114 prefixEnd_627114 := by exact prefixLift 627114
  have htrace : WordTrace (prefixWord ++ tailWord_627114) baseStart_627114 baseEnd_627114 := by
    simpa [prefixWord, tailWord_627114, baseEnd_627114] using wordTrace_append hprefix tailTrace_627114
  have hstable : (prefixWord ++ tailWord_627114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627114).length < 2 ^ (prefixWord ++ tailWord_627114).sum := by decide
  have hdescent : baseEnd_627114 < baseStart_627114 := by decide
  rcases family_descends (prefixWord ++ tailWord_627114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627167 : List Nat := [1, 1, 2, 3, 3, 2, 8]
def baseStart_627167 : Nat := 118140960795 + 627167 * 2 ^ 59
def prefixEnd_627167 : Nat := 4983230072969 + 3 ^ 40 * 627167 * 2
def baseEnd_627167 : Nat := 31806234235896586659577

theorem tailTrace_627167 : CollatzResearch.WordTrace tailWord_627167 prefixEnd_627167 31806234235896586659577 := by
  unfold tailWord_627167
  simp only [CollatzResearch.WordTrace]
  refine ⟨22874659718888545441119755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15249773145925696960746503 22874659718888545441119755)
  ·
    refine ⟨34311989578332818161679633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22874659718888545441119755 34311989578332818161679633)
    ·
      refine ⟨25733992183749613621259725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34311989578332818161679633 25733992183749613621259725)
      ·
        refine ⟨9650247068906105107972397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25733992183749613621259725 9650247068906105107972397)
        ·
          refine ⟨3618842650839789415489649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9650247068906105107972397 3618842650839789415489649)
          ·
            refine ⟨2714131988129842061617237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3618842650839789415489649 2714131988129842061617237)
            ·
              refine ⟨31806234235896586659577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2714131988129842061617237 31806234235896586659577)
              ·
                rfl

theorem cell20_627167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_627167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627167 prefixEnd_627167 := by exact prefixLift 627167
  have htrace : WordTrace (prefixWord ++ tailWord_627167) baseStart_627167 baseEnd_627167 := by
    simpa [prefixWord, tailWord_627167, baseEnd_627167] using wordTrace_append hprefix tailTrace_627167
  have hstable : (prefixWord ++ tailWord_627167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627167).length < 2 ^ (prefixWord ++ tailWord_627167).sum := by decide
  have hdescent : baseEnd_627167 < baseStart_627167 := by decide
  rcases family_descends (prefixWord ++ tailWord_627167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627173 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 4]
def baseStart_627173 : Nat := 118140960795 + 627173 * 2 ^ 59
def prefixEnd_627173 : Nat := 4983230072969 + 3 ^ 40 * 627173 * 2
def baseEnd_627173 : Nat := 286258846686559925736169

theorem tailTrace_627173 : CollatzResearch.WordTrace tailWord_627173 prefixEnd_627173 286258846686559925736169 := by
  unfold tailWord_627173
  simp only [CollatzResearch.WordTrace]
  refine ⟨22874878556866808465838173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15249919037911205643892115 22874878556866808465838173)
  ·
    refine ⟨8578079458825053174689315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22874878556866808465838173 8578079458825053174689315)
    ·
      refine ⟨12867119188237579762033973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578079458825053174689315 12867119188237579762033973)
      ·
        refine ⟨1206292423897273102690685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12867119188237579762033973 1206292423897273102690685)
        ·
          refine ⟨452359658961477413509007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1206292423897273102690685 452359658961477413509007)
          ·
            refine ⟨678539488442216120263511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452359658961477413509007 678539488442216120263511)
            ·
              refine ⟨1017809232663324180395267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678539488442216120263511 1017809232663324180395267)
              ·
                refine ⟨1526713848994986270592901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017809232663324180395267 1526713848994986270592901)
                ·
                  refine ⟨286258846686559925736169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526713848994986270592901 286258846686559925736169)
                  ·
                    rfl

theorem cell20_627173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_627173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627173 prefixEnd_627173 := by exact prefixLift 627173
  have htrace : WordTrace (prefixWord ++ tailWord_627173) baseStart_627173 baseEnd_627173 := by
    simpa [prefixWord, tailWord_627173, baseEnd_627173] using wordTrace_append hprefix tailTrace_627173
  have hstable : (prefixWord ++ tailWord_627173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627173).length < 2 ^ (prefixWord ++ tailWord_627173).sum := by decide
  have hdescent : baseEnd_627173 < baseStart_627173 := by decide
  rcases family_descends (prefixWord ++ tailWord_627173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627205 : List Nat := [1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_627205 : Nat := 118140960795 + 627205 * 2 ^ 59
def prefixEnd_627205 : Nat := 4983230072969 + 3 ^ 40 * 627205 * 2
def baseEnd_627205 : Nat := 95424484119503345556457

theorem tailTrace_627205 : CollatzResearch.WordTrace tailWord_627205 prefixEnd_627205 95424484119503345556457 := by
  unfold tailWord_627205
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876045692750877931003069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15250697128500585287335379 22876045692750877931003069)
  ·
    refine ⟨8578517134781579224126151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22876045692750877931003069 8578517134781579224126151)
    ·
      refine ⟨12867775702172368836189227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578517134781579224126151 12867775702172368836189227)
      ·
        refine ⟨19301663553258553254283841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12867775702172368836189227 19301663553258553254283841)
        ·
          refine ⟨14476247664943914940712881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19301663553258553254283841 14476247664943914940712881)
          ·
            refine ⟨10857185748707936205534661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14476247664943914940712881 10857185748707936205534661)
            ·
              refine ⟨2035722327882738038537749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10857185748707936205534661 2035722327882738038537749)
              ·
                refine ⟨95424484119503345556457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2035722327882738038537749 95424484119503345556457)
                ·
                  rfl

theorem cell20_627205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_627205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627205 prefixEnd_627205 := by exact prefixLift 627205
  have htrace : WordTrace (prefixWord ++ tailWord_627205) baseStart_627205 baseEnd_627205 := by
    simpa [prefixWord, tailWord_627205, baseEnd_627205] using wordTrace_append hprefix tailTrace_627205
  have hstable : (prefixWord ++ tailWord_627205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627205).length < 2 ^ (prefixWord ++ tailWord_627205).sum := by decide
  have hdescent : baseEnd_627205 < baseStart_627205 := by decide
  rcases family_descends (prefixWord ++ tailWord_627205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627281 : List Nat := [1, 2, 2, 1, 3, 4, 7]
def baseStart_627281 : Nat := 118140960795 + 627281 * 2 ^ 59
def prefixEnd_627281 : Nat := 4983230072969 + 3 ^ 40 * 627281 * 2
def baseEnd_627281 : Nat := 31812015647710172237303

theorem tailTrace_627281 : CollatzResearch.WordTrace tailWord_627281 prefixEnd_627281 31812015647710172237303 := by
  unfold tailWord_627281
  simp only [CollatzResearch.WordTrace]
  refine ⟨22878817640475542910769697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15252545093650361940513131 22878817640475542910769697)
  ·
    refine ⟨17159113230356657183077273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22878817640475542910769697 17159113230356657183077273)
    ·
      refine ⟨12869334922767492887307955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17159113230356657183077273 12869334922767492887307955)
      ·
        refine ⟨19304002384151239330961933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12869334922767492887307955 19304002384151239330961933)
        ·
          refine ⟨7239000894056714749110725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19304002384151239330961933 7239000894056714749110725)
          ·
            refine ⟨1357312667635634015458261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7239000894056714749110725 1357312667635634015458261)
            ·
              refine ⟨31812015647710172237303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1357312667635634015458261 31812015647710172237303)
              ·
                rfl

theorem cell20_627281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_627281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627281 prefixEnd_627281 := by exact prefixLift 627281
  have htrace : WordTrace (prefixWord ++ tailWord_627281) baseStart_627281 baseEnd_627281 := by
    simpa [prefixWord, tailWord_627281, baseEnd_627281] using wordTrace_append hprefix tailTrace_627281
  have hstable : (prefixWord ++ tailWord_627281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627281).length < 2 ^ (prefixWord ++ tailWord_627281).sum := by decide
  have hdescent : baseEnd_627281 < baseStart_627281 := by decide
  rcases family_descends (prefixWord ++ tailWord_627281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627284 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_627284 : Nat := 118140960795 + 627284 * 2 ^ 59
def prefixEnd_627284 : Nat := 4983230072969 + 3 ^ 40 * 627284 * 2
def baseEnd_627284 : Nat := 286309510111136873035715

theorem tailTrace_627284 : CollatzResearch.WordTrace tailWord_627284 prefixEnd_627284 286309510111136873035715 := by
  unfold tailWord_627284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439463529732337211564453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15252618039643116282085937 11439463529732337211564453)
  ·
    refine ⟨2144899411824813227168335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11439463529732337211564453 2144899411824813227168335)
    ·
      refine ⟨3217349117737219840752503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144899411824813227168335 3217349117737219840752503)
      ·
        refine ⟨4826023676605829761128755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217349117737219840752503 4826023676605829761128755)
        ·
          refine ⟨7239035514908744641693133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826023676605829761128755 7239035514908744641693133)
          ·
            refine ⟨2714638318090779240634925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7239035514908744641693133 2714638318090779240634925)
            ·
              refine ⟨1017989369284042215238097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2714638318090779240634925 1017989369284042215238097)
              ·
                refine ⟨763492026963031661428573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017989369284042215238097 763492026963031661428573)
                ·
                  refine ⟨286309510111136873035715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763492026963031661428573 286309510111136873035715)
                  ·
                    rfl

theorem cell20_627284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_627284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627284 prefixEnd_627284 := by exact prefixLift 627284
  have htrace : WordTrace (prefixWord ++ tailWord_627284) baseStart_627284 baseEnd_627284 := by
    simpa [prefixWord, tailWord_627284, baseEnd_627284] using wordTrace_append hprefix tailTrace_627284
  have hstable : (prefixWord ++ tailWord_627284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627284).length < 2 ^ (prefixWord ++ tailWord_627284).sum := by decide
  have hdescent : baseEnd_627284 < baseStart_627284 := by decide
  rcases family_descends (prefixWord ++ tailWord_627284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627301 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 3]
def baseStart_627301 : Nat := 118140960795 + 627301 * 2 ^ 59
def prefixEnd_627301 : Nat := 4983230072969 + 3 ^ 40 * 627301 * 2
def baseEnd_627301 : Nat := 286317269374360369468979

theorem tailTrace_627301 : CollatzResearch.WordTrace tailWord_627301 prefixEnd_627301 286317269374360369468979 := by
  unfold tailWord_627301
  simp only [CollatzResearch.WordTrace]
  refine ⟨22879547100403086326497757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15253031400268724217665171 22879547100403086326497757)
  ·
    refine ⟨8579830162651157372436659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22879547100403086326497757 8579830162651157372436659)
    ·
      refine ⟨12869745243976736058654989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8579830162651157372436659 12869745243976736058654989)
      ·
        refine ⟨4826154466491276021995621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12869745243976736058654989 4826154466491276021995621)
        ·
          refine ⟨904903962467114254124179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4826154466491276021995621 904903962467114254124179)
          ·
            refine ⟨1357355943700671381186269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904903962467114254124179 1357355943700671381186269)
            ·
              refine ⟨509008478887751767944851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1357355943700671381186269 509008478887751767944851)
              ·
                refine ⟨763512718331627651917277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509008478887751767944851 763512718331627651917277)
                ·
                  refine ⟨286317269374360369468979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763512718331627651917277 286317269374360369468979)
                  ·
                    rfl

theorem cell20_627301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_627301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627301 prefixEnd_627301 := by exact prefixLift 627301
  have htrace : WordTrace (prefixWord ++ tailWord_627301) baseStart_627301 baseEnd_627301 := by
    simpa [prefixWord, tailWord_627301, baseEnd_627301] using wordTrace_append hprefix tailTrace_627301
  have hstable : (prefixWord ++ tailWord_627301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627301).length < 2 ^ (prefixWord ++ tailWord_627301).sum := by decide
  have hdescent : baseEnd_627301 < baseStart_627301 := by decide
  rcases family_descends (prefixWord ++ tailWord_627301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627325 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 2]
def baseStart_627325 : Nat := 118140960795 + 627325 * 2 ^ 59
def prefixEnd_627325 : Nat := 4983230072969 + 3 ^ 40 * 627325 * 2
def baseEnd_627325 : Nat := 286328223628322952668881

theorem tailTrace_627325 : CollatzResearch.WordTrace tailWord_627325 prefixEnd_627325 286328223628322952668881 := by
  unfold tailWord_627325
  simp only [CollatzResearch.WordTrace]
  refine ⟨22880422452316138425371429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15253614968210758950247619 22880422452316138425371429)
  ·
    refine ⟨4290079209809275954757143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22880422452316138425371429 4290079209809275954757143)
    ·
      refine ⟨6435118814713913932135715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4290079209809275954757143 6435118814713913932135715)
      ·
        refine ⟨9652678222070870898203573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6435118814713913932135715 9652678222070870898203573)
        ·
          refine ⟨904938583319144146706585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9652678222070870898203573 904938583319144146706585)
          ·
            refine ⟨678703937489358110029939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904938583319144146706585 678703937489358110029939)
            ·
              refine ⟨1018055906234037165044909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678703937489358110029939 1018055906234037165044909)
              ·
                refine ⟨381770964837763936891841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1018055906234037165044909 381770964837763936891841)
                ·
                  refine ⟨286328223628322952668881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381770964837763936891841 286328223628322952668881)
                  ·
                    rfl

theorem cell20_627325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_627325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627325 prefixEnd_627325 := by exact prefixLift 627325
  have htrace : WordTrace (prefixWord ++ tailWord_627325) baseStart_627325 baseEnd_627325 := by
    simpa [prefixWord, tailWord_627325, baseEnd_627325] using wordTrace_append hprefix tailTrace_627325
  have hstable : (prefixWord ++ tailWord_627325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627325).length < 2 ^ (prefixWord ++ tailWord_627325).sum := by decide
  have hdescent : baseEnd_627325 < baseStart_627325 := by decide
  rcases family_descends (prefixWord ++ tailWord_627325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627346 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_627346 : Nat := 118140960795 + 627346 * 2 ^ 59
def prefixEnd_627346 : Nat := 4983230072969 + 3 ^ 40 * 627346 * 2
def baseEnd_627346 : Nat := 286337808600540212968795

theorem tailTrace_627346 : CollatzResearch.WordTrace tailWord_627346 prefixEnd_627346 286337808600540212968795 := by
  unfold tailWord_627346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720297096310014752971473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15254125590160039341257261 5720297096310014752971473)
  ·
    refine ⟨4290222822232511064728605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5720297096310014752971473 4290222822232511064728605)
    ·
      refine ⟨1608833558337191649273227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4290222822232511064728605 1608833558337191649273227)
      ·
        refine ⟨2413250337505787473909841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608833558337191649273227 2413250337505787473909841)
        ·
          refine ⟨1809937753129340605432381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413250337505787473909841 1809937753129340605432381)
          ·
            refine ⟨678726657423502727037143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1809937753129340605432381 678726657423502727037143)
            ·
              refine ⟨1018089986135254090555715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678726657423502727037143 1018089986135254090555715)
              ·
                refine ⟨1527134979202881135833573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018089986135254090555715 1527134979202881135833573)
                ·
                  refine ⟨286337808600540212968795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527134979202881135833573 286337808600540212968795)
                  ·
                    rfl

theorem cell20_627346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_627346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627346 prefixEnd_627346 := by exact prefixLift 627346
  have htrace : WordTrace (prefixWord ++ tailWord_627346) baseStart_627346 baseEnd_627346 := by
    simpa [prefixWord, tailWord_627346, baseEnd_627346] using wordTrace_append hprefix tailTrace_627346
  have hstable : (prefixWord ++ tailWord_627346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627346).length < 2 ^ (prefixWord ++ tailWord_627346).sum := by decide
  have hdescent : baseEnd_627346 < baseStart_627346 := by decide
  rcases family_descends (prefixWord ++ tailWord_627346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627357 : List Nat := [1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_627357 : Nat := 118140960795 + 627357 * 2 ^ 59
def prefixEnd_627357 : Nat := 4983230072969 + 3 ^ 40 * 627357 * 2
def baseEnd_627357 : Nat := 95447609766757687867361

theorem tailTrace_627357 : CollatzResearch.WordTrace tailWord_627357 prefixEnd_627357 95447609766757687867361 := by
  unfold tailWord_627357
  simp only [CollatzResearch.WordTrace]
  refine ⟨22881589588200207890536325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15254393058800138593690883 22881589588200207890536325)
  ·
    refine ⟨4290298047787538979475561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22881589588200207890536325 4290298047787538979475561)
    ·
      refine ⟨3217723535840654234606671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4290298047787538979475561 3217723535840654234606671)
      ·
        refine ⟨4826585303760981351910007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217723535840654234606671 4826585303760981351910007)
        ·
          refine ⟨7239877955641472027865011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826585303760981351910007 7239877955641472027865011)
          ·
            refine ⟨10859816933462208041797517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239877955641472027865011 10859816933462208041797517)
            ·
              refine ⟨4072431350048328015674069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10859816933462208041797517 4072431350048328015674069)
              ·
                refine ⟨95447609766757687867361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4072431350048328015674069 95447609766757687867361)
                ·
                  rfl

theorem cell20_627357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_627357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627357 prefixEnd_627357 := by exact prefixLift 627357
  have htrace : WordTrace (prefixWord ++ tailWord_627357) baseStart_627357 baseEnd_627357 := by
    simpa [prefixWord, tailWord_627357, baseEnd_627357] using wordTrace_append hprefix tailTrace_627357
  have hstable : (prefixWord ++ tailWord_627357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627357).length < 2 ^ (prefixWord ++ tailWord_627357).sum := by decide
  have hdescent : baseEnd_627357 < baseStart_627357 := by decide
  rcases family_descends (prefixWord ++ tailWord_627357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627360 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_627360 : Nat := 118140960795 + 627360 * 2 ^ 59
def prefixEnd_627360 : Nat := 4983230072969 + 3 ^ 40 * 627360 * 2
def baseEnd_627360 : Nat := 286344198582018386502071

theorem tailTrace_627360 : CollatzResearch.WordTrace tailWord_627360 prefixEnd_627360 286344198582018386502071 := by
  unfold tailWord_627360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11440849503594669701447767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15254466004792892935263689 11440849503594669701447767)
  ·
    refine ⟨17161274255392004552171651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11440849503594669701447767 17161274255392004552171651)
    ·
      refine ⟨25741911383088006828257477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17161274255392004552171651 25741911383088006828257477)
      ·
        refine ⟨4826608384329001280298277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25741911383088006828257477 4826608384329001280298277)
        ·
          refine ⟨904989072061687740055927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4826608384329001280298277 904989072061687740055927)
          ·
            refine ⟨1357483608092531610083891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904989072061687740055927 1357483608092531610083891)
            ·
              refine ⟨2036225412138797415125837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357483608092531610083891 2036225412138797415125837)
              ·
                refine ⟨763584529552049030672189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036225412138797415125837 763584529552049030672189)
                ·
                  refine ⟨286344198582018386502071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763584529552049030672189 286344198582018386502071)
                  ·
                    rfl

theorem cell20_627360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_627360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627360 prefixEnd_627360 := by exact prefixLift 627360
  have htrace : WordTrace (prefixWord ++ tailWord_627360) baseStart_627360 baseEnd_627360 := by
    simpa [prefixWord, tailWord_627360, baseEnd_627360] using wordTrace_append hprefix tailTrace_627360
  have hstable : (prefixWord ++ tailWord_627360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627360).length < 2 ^ (prefixWord ++ tailWord_627360).sum := by decide
  have hdescent : baseEnd_627360 < baseStart_627360 := by decide
  rcases family_descends (prefixWord ++ tailWord_627360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627440 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_627440 : Nat := 118140960795 + 627440 * 2 ^ 59
def prefixEnd_627440 : Nat := 4983230072969 + 3 ^ 40 * 627440 * 2
def baseEnd_627440 : Nat := 286380712761893663835077

theorem tailTrace_627440 : CollatzResearch.WordTrace tailWord_627440 prefixEnd_627440 286380712761893663835077 := by
  unfold tailWord_627440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442308423449756532903887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15256411231266342043871849 11442308423449756532903887)
  ·
    refine ⟨17163462635174634799355831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442308423449756532903887 17163462635174634799355831)
    ·
      refine ⟨25745193952761952199033747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17163462635174634799355831 25745193952761952199033747)
      ·
        refine ⟨38617790929142928298550621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25745193952761952199033747 38617790929142928298550621)
        ·
          refine ⟨14481671598428598111956483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38617790929142928298550621 14481671598428598111956483)
          ·
            refine ⟨21722507397642897167934725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14481671598428598111956483 21722507397642897167934725)
            ·
              refine ⟨4072970137058043218987761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21722507397642897167934725 4072970137058043218987761)
              ·
                refine ⟨3054727602793532414240821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072970137058043218987761 3054727602793532414240821)
                ·
                  refine ⟨286380712761893663835077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3054727602793532414240821 286380712761893663835077)
                  ·
                    rfl

theorem cell20_627440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_627440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627440 prefixEnd_627440 := by exact prefixLift 627440
  have htrace : WordTrace (prefixWord ++ tailWord_627440) baseStart_627440 baseEnd_627440 := by
    simpa [prefixWord, tailWord_627440, baseEnd_627440] using wordTrace_append hprefix tailTrace_627440
  have hstable : (prefixWord ++ tailWord_627440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627440).length < 2 ^ (prefixWord ++ tailWord_627440).sum := by decide
  have hdescent : baseEnd_627440 < baseStart_627440 := by decide
  rcases family_descends (prefixWord ++ tailWord_627440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627447 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_627447 : Nat := 118140960795 + 627447 * 2 ^ 59
def prefixEnd_627447 : Nat := 4983230072969 + 3 ^ 40 * 627447 * 2
def baseEnd_627447 : Nat := 286383907752632750601715

theorem tailTrace_627447 : CollatzResearch.WordTrace tailWord_627447 prefixEnd_627447 286383907752632750601715 := by
  unfold tailWord_627447
  simp only [CollatzResearch.WordTrace]
  refine ⟨22884872157874153261312595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15256581438582768840875063 22884872157874153261312595)
  ·
    refine ⟨34327308236811229891968893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22884872157874153261312595 34327308236811229891968893)
    ·
      refine ⟨12872740588804211209488335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34327308236811229891968893 12872740588804211209488335)
      ·
        refine ⟨19309110883206316814232503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872740588804211209488335 19309110883206316814232503)
        ·
          refine ⟨28963666324809475221348755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19309110883206316814232503 28963666324809475221348755)
          ·
            refine ⟨43445499487214212832023133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28963666324809475221348755 43445499487214212832023133)
            ·
              refine ⟨16292062307705329812008675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43445499487214212832023133 16292062307705329812008675)
              ·
                refine ⟨24438093461557994718013013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16292062307705329812008675 24438093461557994718013013)
                ·
                  refine ⟨286383907752632750601715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24438093461557994718013013 286383907752632750601715)
                  ·
                    rfl

theorem cell20_627447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_627447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627447 prefixEnd_627447 := by exact prefixLift 627447
  have htrace : WordTrace (prefixWord ++ tailWord_627447) baseStart_627447 baseEnd_627447 := by
    simpa [prefixWord, tailWord_627447, baseEnd_627447] using wordTrace_append hprefix tailTrace_627447
  have hstable : (prefixWord ++ tailWord_627447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627447).length < 2 ^ (prefixWord ++ tailWord_627447).sum := by decide
  have hdescent : baseEnd_627447 < baseStart_627447 := by decide
  rcases family_descends (prefixWord ++ tailWord_627447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627464 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_627464 : Nat := 118140960795 + 627464 * 2 ^ 59
def prefixEnd_627464 : Nat := 4983230072969 + 3 ^ 40 * 627464 * 2
def baseEnd_627464 : Nat := 286391667015856247034979

theorem tailTrace_627464 : CollatzResearch.WordTrace tailWord_627464 prefixEnd_627464 286391667015856247034979 := by
  unfold tailWord_627464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442746099406282582340723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15256994799208376776454297 11442746099406282582340723)
  ·
    refine ⟨17164119149109423873511085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442746099406282582340723 17164119149109423873511085)
    ·
      refine ⟨6436544680916033952566657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17164119149109423873511085 6436544680916033952566657)
      ·
        refine ⟨4827408510687025464424993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6436544680916033952566657 4827408510687025464424993)
        ·
          refine ⟨3620556383015269098318745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827408510687025464424993 3620556383015269098318745)
          ·
            refine ⟨2715417287261451823739059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3620556383015269098318745 2715417287261451823739059)
            ·
              refine ⟨4073125930892177735608589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715417287261451823739059 4073125930892177735608589)
              ·
                refine ⟨1527422224084566650853221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4073125930892177735608589 1527422224084566650853221)
                ·
                  refine ⟨286391667015856247034979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527422224084566650853221 286391667015856247034979)
                  ·
                    rfl

theorem cell20_627464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_627464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627464 prefixEnd_627464 := by exact prefixLift 627464
  have htrace : WordTrace (prefixWord ++ tailWord_627464) baseStart_627464 baseEnd_627464 := by
    simpa [prefixWord, tailWord_627464, baseEnd_627464] using wordTrace_append hprefix tailTrace_627464
  have hstable : (prefixWord ++ tailWord_627464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627464).length < 2 ^ (prefixWord ++ tailWord_627464).sum := by decide
  have hdescent : baseEnd_627464 < baseStart_627464 := by decide
  rcases family_descends (prefixWord ++ tailWord_627464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627488 : List Nat := [2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_627488 : Nat := 118140960795 + 627488 * 2 ^ 59
def prefixEnd_627488 : Nat := 4983230072969 + 3 ^ 40 * 627488 * 2
def baseEnd_627488 : Nat := 95467540423272943411627

theorem tailTrace_627488 : CollatzResearch.WordTrace tailWord_627488 prefixEnd_627488 95467540423272943411627 := by
  unfold tailWord_627488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443183775362808631777559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15257578367150411509036745 11443183775362808631777559)
  ·
    refine ⟨17164775663044212947666339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11443183775362808631777559 17164775663044212947666339)
    ·
      refine ⟨25747163494566319421499509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17164775663044212947666339 25747163494566319421499509)
      ·
        refine ⟨2413796577615592445765579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25747163494566319421499509 2413796577615592445765579)
        ·
          refine ⟨3620694866423388668648369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413796577615592445765579 3620694866423388668648369)
          ·
            refine ⟨2715521149817541501486277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3620694866423388668648369 2715521149817541501486277)
            ·
              refine ⟨509160215590789031528677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2715521149817541501486277 509160215590789031528677)
              ·
                refine ⟨95467540423272943411627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509160215590789031528677 95467540423272943411627)
                ·
                  rfl

theorem cell20_627488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_627488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627488 prefixEnd_627488 := by exact prefixLift 627488
  have htrace : WordTrace (prefixWord ++ tailWord_627488) baseStart_627488 baseEnd_627488 := by
    simpa [prefixWord, tailWord_627488, baseEnd_627488] using wordTrace_append hprefix tailTrace_627488
  have hstable : (prefixWord ++ tailWord_627488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627488).length < 2 ^ (prefixWord ++ tailWord_627488).sum := by decide
  have hdescent : baseEnd_627488 < baseStart_627488 := by decide
  rcases family_descends (prefixWord ++ tailWord_627488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627509 : List Nat := [1, 3, 3, 1, 3, 1, 8]
def baseStart_627509 : Nat := 118140960795 + 627509 * 2 ^ 59
def prefixEnd_627509 : Nat := 4983230072969 + 3 ^ 40 * 627509 * 2
def baseEnd_627509 : Nat := 31823578471337343392755

theorem tailTrace_627509 : CollatzResearch.WordTrace tailWord_627509 prefixEnd_627509 31823578471337343392755 := by
  unfold tailWord_627509
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887133483649537850069581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15258088989099691900046387 22887133483649537850069581)
  ·
    refine ⟨8582675056368576693776093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22887133483649537850069581 8582675056368576693776093)
    ·
      refine ⟨3218503146138216260166035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8582675056368576693776093 3218503146138216260166035)
      ·
        refine ⟨4827754719207324390249053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218503146138216260166035 4827754719207324390249053)
        ·
          refine ⟨1810408019702746646343395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4827754719207324390249053 1810408019702746646343395)
          ·
            refine ⟨2715612029554119969515093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810408019702746646343395 2715612029554119969515093)
            ·
              refine ⟨31823578471337343392755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2715612029554119969515093 31823578471337343392755)
              ·
                rfl

theorem cell20_627509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_627509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627509 prefixEnd_627509 := by exact prefixLift 627509
  have htrace : WordTrace (prefixWord ++ tailWord_627509) baseStart_627509 baseEnd_627509 := by
    simpa [prefixWord, tailWord_627509, baseEnd_627509] using wordTrace_append hprefix tailTrace_627509
  have hstable : (prefixWord ++ tailWord_627509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627509).length < 2 ^ (prefixWord ++ tailWord_627509).sum := by decide
  have hdescent : baseEnd_627509 < baseStart_627509 := by decide
  rcases family_descends (prefixWord ++ tailWord_627509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627519 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_627519 : Nat := 118140960795 + 627519 * 2 ^ 59
def prefixEnd_627519 : Nat := 4983230072969 + 3 ^ 40 * 627519 * 2
def baseEnd_627519 : Nat := 286416770514520500201421

theorem tailTrace_627519 : CollatzResearch.WordTrace tailWord_627519 prefixEnd_627519 286416770514520500201421 := by
  unfold tailWord_627519
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887498213613309557933611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15258332142408873038622407 22887498213613309557933611)
  ·
    refine ⟨34331247320419964336900417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22887498213613309557933611 34331247320419964336900417)
    ·
      refine ⟨25748435490314973252675313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34331247320419964336900417 25748435490314973252675313)
      ·
        refine ⟨19311326617736229939506485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25748435490314973252675313 19311326617736229939506485)
        ·
          refine ⟨1810436870412771556828733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19311326617736229939506485 1810436870412771556828733)
          ·
            refine ⟨678913826404789333810775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1810436870412771556828733 678913826404789333810775)
            ·
              refine ⟨1018370739607184000716163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678913826404789333810775 1018370739607184000716163)
              ·
                refine ⟨1527556109410776001074245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018370739607184000716163 1527556109410776001074245)
                ·
                  refine ⟨286416770514520500201421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527556109410776001074245 286416770514520500201421)
                  ·
                    rfl

theorem cell20_627519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_627519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627519 prefixEnd_627519 := by exact prefixLift 627519
  have htrace : WordTrace (prefixWord ++ tailWord_627519) baseStart_627519 baseEnd_627519 := by
    simpa [prefixWord, tailWord_627519, baseEnd_627519] using wordTrace_append hprefix tailTrace_627519
  have hstable : (prefixWord ++ tailWord_627519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627519).length < 2 ^ (prefixWord ++ tailWord_627519).sum := by decide
  have hdescent : baseEnd_627519 < baseStart_627519 := by decide
  rcases family_descends (prefixWord ++ tailWord_627519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627633 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_627633 : Nat := 118140960795 + 627633 * 2 ^ 59
def prefixEnd_627633 : Nat := 4983230072969 + 3 ^ 40 * 627633 * 2
def baseEnd_627633 : Nat := 286468803220842770400955

theorem tailTrace_627633 : CollatzResearch.WordTrace tailWord_627633 prefixEnd_627633 286468803220842770400955 := by
  unfold tailWord_627633
  simp only [CollatzResearch.WordTrace]
  refine ⟨22891656135200307027583553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15261104090133538018389035 22891656135200307027583553)
  ·
    refine ⟨17168742101400230270687665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22891656135200307027583553 17168742101400230270687665)
    ·
      refine ⟨12876556576050172703015749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17168742101400230270687665 12876556576050172703015749)
      ·
        refine ⟨2414354358009407381815453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12876556576050172703015749 2414354358009407381815453)
        ·
          refine ⟨905382884253527768180795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2414354358009407381815453 905382884253527768180795)
          ·
            refine ⟨1358074326380291652271193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905382884253527768180795 1358074326380291652271193)
            ·
              refine ⟨1018555744785218739203395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358074326380291652271193 1018555744785218739203395)
              ·
                refine ⟨1527833617177828108805093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018555744785218739203395 1527833617177828108805093)
                ·
                  refine ⟨286468803220842770400955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527833617177828108805093 286468803220842770400955)
                  ·
                    rfl

theorem cell20_627633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_627633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627633 prefixEnd_627633 := by exact prefixLift 627633
  have htrace : WordTrace (prefixWord ++ tailWord_627633) baseStart_627633 baseEnd_627633 := by
    simpa [prefixWord, tailWord_627633, baseEnd_627633] using wordTrace_append hprefix tailTrace_627633
  have hstable : (prefixWord ++ tailWord_627633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627633).length < 2 ^ (prefixWord ++ tailWord_627633).sum := by decide
  have hdescent : baseEnd_627633 < baseStart_627633 := by decide
  rcases family_descends (prefixWord ++ tailWord_627633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627698 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_627698 : Nat := 118140960795 + 627698 * 2 ^ 59
def prefixEnd_627698 : Nat := 4983230072969 + 3 ^ 40 * 627698 * 2
def baseEnd_627698 : Nat := 286498470991991433234023

theorem tailTrace_627698 : CollatzResearch.WordTrace tailWord_627698 prefixEnd_627698 286498470991991433234023 := by
  unfold tailWord_627698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723506719991205782174937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15262684586643215419133165 5723506719991205782174937)
  ·
    refine ⟨4292630039993404336631203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5723506719991205782174937 4292630039993404336631203)
    ·
      refine ⟨6438945059990106504946805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4292630039993404336631203 6438945059990106504946805)
      ·
        refine ⟨603651099374072484838763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6438945059990106504946805 603651099374072484838763)
        ·
          refine ⟨905476649061108727258145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603651099374072484838763 905476649061108727258145)
          ·
            refine ⟨679107486795831545443609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905476649061108727258145 679107486795831545443609)
            ·
              refine ⟨509330615096873659082707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679107486795831545443609 509330615096873659082707)
              ·
                refine ⟨763995922645310488624061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509330615096873659082707 763995922645310488624061)
                ·
                  refine ⟨286498470991991433234023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763995922645310488624061 286498470991991433234023)
                  ·
                    rfl

theorem cell20_627698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_627698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627698 prefixEnd_627698 := by exact prefixLift 627698
  have htrace : WordTrace (prefixWord ++ tailWord_627698) baseStart_627698 baseEnd_627698 := by
    simpa [prefixWord, tailWord_627698, baseEnd_627698] using wordTrace_append hprefix tailTrace_627698
  have hstable : (prefixWord ++ tailWord_627698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627698).length < 2 ^ (prefixWord ++ tailWord_627698).sum := by decide
  have hdescent : baseEnd_627698 < baseStart_627698 := by decide
  rcases family_descends (prefixWord ++ tailWord_627698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627702 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_627702 : Nat := 118140960795 + 627702 * 2 ^ 59
def prefixEnd_627702 : Nat := 4983230072969 + 3 ^ 40 * 627702 * 2
def baseEnd_627702 : Nat := 286500296700985197100673

theorem tailTrace_627702 : CollatzResearch.WordTrace tailWord_627702 prefixEnd_627702 286500296700985197100673 := by
  unfold tailWord_627702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430885798246895738240335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15262781847966887874563573 1430885798246895738240335)
  ·
    refine ⟨2146328697370343607360503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430885798246895738240335 2146328697370343607360503)
    ·
      refine ⟨3219493046055515411040755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146328697370343607360503 3219493046055515411040755)
      ·
        refine ⟨4829239569083273116561133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219493046055515411040755 4829239569083273116561133)
        ·
          refine ⟨1810964838406227418710425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4829239569083273116561133 1810964838406227418710425)
          ·
            refine ⟨1358223628804670564032819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810964838406227418710425 1358223628804670564032819)
            ·
              refine ⟨2037335443207005846049229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358223628804670564032819 2037335443207005846049229)
              ·
                refine ⟨764000791202627192268461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2037335443207005846049229 764000791202627192268461)
                ·
                  refine ⟨286500296700985197100673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764000791202627192268461 286500296700985197100673)
                  ·
                    rfl

theorem cell20_627702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_627702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627702 prefixEnd_627702 := by exact prefixLift 627702
  have htrace : WordTrace (prefixWord ++ tailWord_627702) baseStart_627702 baseEnd_627702 := by
    simpa [prefixWord, tailWord_627702, baseEnd_627702] using wordTrace_append hprefix tailTrace_627702
  have hstable : (prefixWord ++ tailWord_627702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627702).length < 2 ^ (prefixWord ++ tailWord_627702).sum := by decide
  have hdescent : baseEnd_627702 < baseStart_627702 := by decide
  rcases family_descends (prefixWord ++ tailWord_627702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627740 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_627740 : Nat := 118140960795 + 627740 * 2 ^ 59
def prefixEnd_627740 : Nat := 4983230072969 + 3 ^ 40 * 627740 * 2
def baseEnd_627740 : Nat := 286517640936425953833851

theorem tailTrace_627740 : CollatzResearch.WordTrace tailWord_627740 prefixEnd_627740 286517640936425953833851 := by
  unfold tailWord_627740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447779372906332150864337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15263705830541776201152449 11447779372906332150864337)
  ·
    refine ⟨8585834529679749113148253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11447779372906332150864337 8585834529679749113148253)
    ·
      refine ⟨3219687948629905917430595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8585834529679749113148253 3219687948629905917430595)
      ·
        refine ⟨4829531922944858876145893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219687948629905917430595 4829531922944858876145893)
        ·
          refine ⟨905537235552161039277355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4829531922944858876145893 905537235552161039277355)
          ·
            refine ⟨1358305853328241558916033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905537235552161039277355 1358305853328241558916033)
            ·
              refine ⟨1018729389996181169187025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358305853328241558916033 1018729389996181169187025)
              ·
                refine ⟨764047042497135876890269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018729389996181169187025 764047042497135876890269)
                ·
                  refine ⟨286517640936425953833851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764047042497135876890269 286517640936425953833851)
                  ·
                    rfl

theorem cell20_627740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_627740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627740 prefixEnd_627740 := by exact prefixLift 627740
  have htrace : WordTrace (prefixWord ++ tailWord_627740) baseStart_627740 baseEnd_627740 := by
    simpa [prefixWord, tailWord_627740, baseEnd_627740] using wordTrace_append hprefix tailTrace_627740
  have hstable : (prefixWord ++ tailWord_627740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627740).length < 2 ^ (prefixWord ++ tailWord_627740).sum := by decide
  have hdescent : baseEnd_627740 < baseStart_627740 := by decide
  rcases family_descends (prefixWord ++ tailWord_627740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627747 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 2]
def baseStart_627747 : Nat := 118140960795 + 627747 * 2 ^ 59
def prefixEnd_627747 : Nat := 4983230072969 + 3 ^ 40 * 627747 * 2
def baseEnd_627747 : Nat := 286520835927165040600489

theorem tailTrace_627747 : CollatzResearch.WordTrace tailWord_627747 prefixEnd_627747 286520835927165040600489 := by
  unfold tailWord_627747
  simp only [CollatzResearch.WordTrace]
  refine ⟨22895814056787304497233495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15263876037858202998155663 22895814056787304497233495)
  ·
    refine ⟨34343721085180956745850243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22895814056787304497233495 34343721085180956745850243)
    ·
      refine ⟨51515581627771435118775365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34343721085180956745850243 51515581627771435118775365)
      ·
        refine ⟨9659171555207144084770381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51515581627771435118775365 9659171555207144084770381)
        ·
          refine ⟨3622189333202679031788893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9659171555207144084770381 3622189333202679031788893)
          ·
            refine ⟨1358320999951004636920835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3622189333202679031788893 1358320999951004636920835)
            ·
              refine ⟨2037481499926506955381253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358320999951004636920835 2037481499926506955381253)
              ·
                refine ⟨382027781236220054133985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2037481499926506955381253 382027781236220054133985)
                ·
                  refine ⟨286520835927165040600489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382027781236220054133985 286520835927165040600489)
                  ·
                    rfl

theorem cell20_627747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2].length) (baseStart_627747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627747 prefixEnd_627747 := by exact prefixLift 627747
  have htrace : WordTrace (prefixWord ++ tailWord_627747) baseStart_627747 baseEnd_627747 := by
    simpa [prefixWord, tailWord_627747, baseEnd_627747] using wordTrace_append hprefix tailTrace_627747
  have hstable : (prefixWord ++ tailWord_627747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627747).length < 2 ^ (prefixWord ++ tailWord_627747).sum := by decide
  have hdescent : baseEnd_627747 < baseStart_627747 := by decide
  rcases family_descends (prefixWord ++ tailWord_627747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627768 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_627768 : Nat := 118140960795 + 627768 * 2 ^ 59
def prefixEnd_627768 : Nat := 4983230072969 + 3 ^ 40 * 627768 * 2
def baseEnd_627768 : Nat := 286530420899382300900403

theorem tailTrace_627768 : CollatzResearch.WordTrace tailWord_627768 prefixEnd_627768 286530420899382300900403 := by
  unfold tailWord_627768
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448289994855612541873979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15264386659807483389165305 11448289994855612541873979)
  ·
    refine ⟨17172434992283418812810969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448289994855612541873979 17172434992283418812810969)
    ·
      refine ⟨12879326244212564109608227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17172434992283418812810969 12879326244212564109608227)
      ·
        refine ⟨19318989366318846164412341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12879326244212564109608227 19318989366318846164412341)
        ·
          refine ⟨1811155253092391827913657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19318989366318846164412341 1811155253092391827913657)
          ·
            refine ⟨1358366439819293870935243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1811155253092391827913657 1358366439819293870935243)
            ·
              refine ⟨2037549659728940806402865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358366439819293870935243 2037549659728940806402865)
              ·
                refine ⟨1528162244796705604802149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037549659728940806402865 1528162244796705604802149)
                ·
                  refine ⟨286530420899382300900403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528162244796705604802149 286530420899382300900403)
                  ·
                    rfl

theorem cell20_627768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_627768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627768 prefixEnd_627768 := by exact prefixLift 627768
  have htrace : WordTrace (prefixWord ++ tailWord_627768) baseStart_627768 baseEnd_627768 := by
    simpa [prefixWord, tailWord_627768, baseEnd_627768] using wordTrace_append hprefix tailTrace_627768
  have hstable : (prefixWord ++ tailWord_627768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627768).length < 2 ^ (prefixWord ++ tailWord_627768).sum := by decide
  have hdescent : baseEnd_627768 < baseStart_627768 := by decide
  rcases family_descends (prefixWord ++ tailWord_627768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627871 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 3]
def baseStart_627871 : Nat := 118140960795 + 627871 * 2 ^ 59
def prefixEnd_627871 : Nat := 4983230072969 + 3 ^ 40 * 627871 * 2
def baseEnd_627871 : Nat := 286577432905971720466649

theorem tailTrace_627871 : CollatzResearch.WordTrace tailWord_627871 prefixEnd_627871 286577432905971720466649 := by
  unfold tailWord_627871
  simp only [CollatzResearch.WordTrace]
  refine ⟨22900336708338073674747467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15266891138892049116498311 22900336708338073674747467)
  ·
    refine ⟨34350505062507110512121201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22900336708338073674747467 34350505062507110512121201)
    ·
      refine ⟨25762878796880332884090901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34350505062507110512121201 25762878796880332884090901)
      ·
        refine ⟨1207634943603765603941761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25762878796880332884090901 1207634943603765603941761)
        ·
          refine ⟨905726207702824202956321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1207634943603765603941761 905726207702824202956321)
          ·
            refine ⟨679294655777118152217241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905726207702824202956321 679294655777118152217241)
            ·
              refine ⟨509470991832838614162931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679294655777118152217241 509470991832838614162931)
              ·
                refine ⟨764206487749257921244397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509470991832838614162931 764206487749257921244397)
                ·
                  refine ⟨286577432905971720466649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764206487749257921244397 286577432905971720466649)
                  ·
                    rfl

theorem cell20_627871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_627871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627871 prefixEnd_627871 := by exact prefixLift 627871
  have htrace : WordTrace (prefixWord ++ tailWord_627871) baseStart_627871 baseEnd_627871 := by
    simpa [prefixWord, tailWord_627871, baseEnd_627871] using wordTrace_append hprefix tailTrace_627871
  have hstable : (prefixWord ++ tailWord_627871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627871).length < 2 ^ (prefixWord ++ tailWord_627871).sum := by decide
  have hdescent : baseEnd_627871 < baseStart_627871 := by decide
  rcases family_descends (prefixWord ++ tailWord_627871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627889 : List Nat := [1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_627889 : Nat := 118140960795 + 627889 * 2 ^ 59
def prefixEnd_627889 : Nat := 4983230072969 + 3 ^ 40 * 627889 * 2
def baseEnd_627889 : Nat := 95528549532147885955525

theorem tailTrace_627889 : CollatzResearch.WordTrace tailWord_627889 prefixEnd_627889 95528549532147885955525 := by
  unfold tailWord_627889
  simp only [CollatzResearch.WordTrace]
  refine ⟨22900993222272862748902721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15267328814848575165935147 22900993222272862748902721)
  ·
    refine ⟨17175744916704647061677041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22900993222272862748902721 17175744916704647061677041)
    ·
      refine ⟨12881808687528485296257781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17175744916704647061677041 12881808687528485296257781)
      ·
        refine ⟨1207669564455795496524167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12881808687528485296257781 1207669564455795496524167)
        ·
          refine ⟨1811504346683693244786251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207669564455795496524167 1811504346683693244786251)
          ·
            refine ⟨2717256520025539867179377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811504346683693244786251 2717256520025539867179377)
            ·
              refine ⟨2037942390019154900384533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717256520025539867179377 2037942390019154900384533)
              ·
                refine ⟨95528549532147885955525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2037942390019154900384533 95528549532147885955525)
                ·
                  rfl

theorem cell20_627889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_627889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627889 prefixEnd_627889 := by exact prefixLift 627889
  have htrace : WordTrace (prefixWord ++ tailWord_627889) baseStart_627889 baseEnd_627889 := by
    simpa [prefixWord, tailWord_627889, baseEnd_627889] using wordTrace_append hprefix tailTrace_627889
  have hstable : (prefixWord ++ tailWord_627889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627889).length < 2 ^ (prefixWord ++ tailWord_627889).sum := by decide
  have hdescent : baseEnd_627889 < baseStart_627889 := by decide
  rcases family_descends (prefixWord ++ tailWord_627889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627906 : List Nat := [3, 5, 1, 1, 10]
def baseStart_627906 : Nat := 118140960795 + 627906 * 2 ^ 59
def prefixEnd_627906 : Nat := 4983230072969 + 3 ^ 40 * 627906 * 2
def baseEnd_627906 : Nat := 3538190220489717954319

theorem tailTrace_627906 : CollatzResearch.WordTrace tailWord_627906 prefixEnd_627906 3538190220489717954319 := by
  unfold tailWord_627906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725403315802818663067893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15267742175474183101514381 5725403315802818663067893)
  ·
    refine ⟨536756560856514249662615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5725403315802818663067893 536756560856514249662615)
    ·
      refine ⟨805134841284771374493923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536756560856514249662615 805134841284771374493923)
      ·
        refine ⟨1207702261927157061740885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805134841284771374493923 1207702261927157061740885)
        ·
          refine ⟨3538190220489717954319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1207702261927157061740885 3538190220489717954319)
          ·
            rfl

theorem cell20_627906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 10].length) (baseStart_627906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627906 prefixEnd_627906 := by exact prefixLift 627906
  have htrace : WordTrace (prefixWord ++ tailWord_627906) baseStart_627906 baseEnd_627906 := by
    simpa [prefixWord, tailWord_627906, baseEnd_627906] using wordTrace_append hprefix tailTrace_627906
  have hstable : (prefixWord ++ tailWord_627906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627906).length < 2 ^ (prefixWord ++ tailWord_627906).sum := by decide
  have hdescent : baseEnd_627906 < baseStart_627906 := by decide
  rcases family_descends (prefixWord ++ tailWord_627906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627954 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_627954 : Nat := 118140960795 + 627954 * 2 ^ 59
def prefixEnd_627954 : Nat := 4983230072969 + 3 ^ 40 * 627954 * 2
def baseEnd_627954 : Nat := 286615316367592320699643

theorem tailTrace_627954 : CollatzResearch.WordTrace tailWord_627954 prefixEnd_627954 286615316367592320699643 := by
  unfold tailWord_627954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725840991759344712504729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15268909311358252566679277 5725840991759344712504729)
  ·
    refine ⟨4294380743819508534378547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5725840991759344712504729 4294380743819508534378547)
    ·
      refine ⟨6441571115729262801567821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4294380743819508534378547 6441571115729262801567821)
      ·
        refine ⟨2415589168398473550587933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6441571115729262801567821 2415589168398473550587933)
        ·
          refine ⟨905845938149427581470475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2415589168398473550587933 905845938149427581470475)
          ·
            refine ⟨1358768907224141372205713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905845938149427581470475 1358768907224141372205713)
            ·
              refine ⟨1019076680418106029154285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358768907224141372205713 1019076680418106029154285)
              ·
                refine ⟨382153755156789760932857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019076680418106029154285 382153755156789760932857)
                ·
                  refine ⟨286615316367592320699643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382153755156789760932857 286615316367592320699643)
                  ·
                    rfl

theorem cell20_627954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_627954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627954 prefixEnd_627954 := by exact prefixLift 627954
  have htrace : WordTrace (prefixWord ++ tailWord_627954) baseStart_627954 baseEnd_627954 := by
    simpa [prefixWord, tailWord_627954, baseEnd_627954] using wordTrace_append hprefix tailTrace_627954
  have hstable : (prefixWord ++ tailWord_627954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627954).length < 2 ^ (prefixWord ++ tailWord_627954).sum := by decide
  have hdescent : baseEnd_627954 < baseStart_627954 := by decide
  rcases family_descends (prefixWord ++ tailWord_627954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627979 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_627979 : Nat := 118140960795 + 627979 * 2 ^ 59
def prefixEnd_627979 : Nat := 4983230072969 + 3 ^ 40 * 627979 * 2
def baseEnd_627979 : Nat := 286626727048803344866207

theorem tailTrace_627979 : CollatzResearch.WordTrace tailWord_627979 prefixEnd_627979 286626727048803344866207 := by
  unfold tailWord_627979
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904275791946808119678991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15269517194631205413119327 22904275791946808119678991)
  ·
    refine ⟨34356413687920212179518487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22904275791946808119678991 34356413687920212179518487)
    ·
      refine ⟨51534620531880318269277731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34356413687920212179518487 51534620531880318269277731)
      ·
        refine ⟨77301930797820477403916597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51534620531880318269277731 77301930797820477403916597)
        ·
          refine ⟨7247056012295669756617181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77301930797820477403916597 7247056012295669756617181)
          ·
            refine ⟨2717646004610876158731443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7247056012295669756617181 2717646004610876158731443)
            ·
              refine ⟨4076469006916314238097165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717646004610876158731443 4076469006916314238097165)
              ·
                refine ⟨1528675877593617839286437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4076469006916314238097165 1528675877593617839286437)
                ·
                  refine ⟨286626727048803344866207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528675877593617839286437 286626727048803344866207)
                  ·
                    rfl

theorem cell20_627979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_627979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627979 prefixEnd_627979 := by exact prefixLift 627979
  have htrace : WordTrace (prefixWord ++ tailWord_627979) baseStart_627979 baseEnd_627979 := by
    simpa [prefixWord, tailWord_627979, baseEnd_627979] using wordTrace_append hprefix tailTrace_627979
  have hstable : (prefixWord ++ tailWord_627979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627979).length < 2 ^ (prefixWord ++ tailWord_627979).sum := by decide
  have hdescent : baseEnd_627979 < baseStart_627979 := by decide
  rcases family_descends (prefixWord ++ tailWord_627979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627999 : List Nat := [1, 1, 2, 4, 5, 1, 2, 4]
def baseStart_627999 : Nat := 118140960795 + 627999 * 2 ^ 59
def prefixEnd_627999 : Nat := 4983230072969 + 3 ^ 40 * 627999 * 2
def baseEnd_627999 : Nat := 95545285197924054733153

theorem tailTrace_627999 : CollatzResearch.WordTrace tailWord_627999 prefixEnd_627999 95545285197924054733153 := by
  unfold tailWord_627999
  simp only [CollatzResearch.WordTrace]
  refine ⟨22905005251874351535407051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15270003501249567690271367 22905005251874351535407051)
  ·
    refine ⟨34357507877811527303110577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22905005251874351535407051 34357507877811527303110577)
    ·
      refine ⟨25768130908358645477332933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34357507877811527303110577 25768130908358645477332933)
      ·
        refine ⟨4831524545317246026999925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25768130908358645477332933 4831524545317246026999925)
        ·
          refine ⟨452955426123491815031243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4831524545317246026999925 452955426123491815031243)
          ·
            refine ⟨679433139185237722546865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452955426123491815031243 679433139185237722546865)
            ·
              refine ⟨509574854388928291910149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679433139185237722546865 509574854388928291910149)
              ·
                refine ⟨95545285197924054733153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509574854388928291910149 95545285197924054733153)
                ·
                  rfl

theorem cell20_627999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_627999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_627999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_627999 prefixEnd_627999 := by exact prefixLift 627999
  have htrace : WordTrace (prefixWord ++ tailWord_627999) baseStart_627999 baseEnd_627999 := by
    simpa [prefixWord, tailWord_627999, baseEnd_627999] using wordTrace_append hprefix tailTrace_627999
  have hstable : (prefixWord ++ tailWord_627999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627999).length < 2 ^ (prefixWord ++ tailWord_627999).sum := by decide
  have hdescent : baseEnd_627999 < baseStart_627999 := by decide
  rcases family_descends (prefixWord ++ tailWord_627999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628003 : List Nat := [1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_628003 : Nat := 118140960795 + 628003 * 2 ^ 59
def prefixEnd_628003 : Nat := 4983230072969 + 3 ^ 40 * 628003 * 2
def baseEnd_628003 : Nat := 95545893767588642688703

theorem tailTrace_628003 : CollatzResearch.WordTrace tailWord_628003 prefixEnd_628003 95545893767588642688703 := by
  unfold tailWord_628003
  simp only [CollatzResearch.WordTrace]
  refine ⟨22905151143859860218552663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15270100762573240145701775 22905151143859860218552663)
  ·
    refine ⟨34357726715789790327828995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22905151143859860218552663 34357726715789790327828995)
    ·
      refine ⟨51536590073684685491743493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34357726715789790327828995 51536590073684685491743493)
      ·
        refine ⟨9663110638815878529701905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51536590073684685491743493 9663110638815878529701905)
        ·
          refine ⟨7247332979111908897276429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9663110638815878529701905 7247332979111908897276429)
          ·
            refine ⟨2717749867166965836478661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7247332979111908897276429 2717749867166965836478661)
            ·
              refine ⟨509578100093806094339749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2717749867166965836478661 509578100093806094339749)
              ·
                refine ⟨95545893767588642688703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509578100093806094339749 95545893767588642688703)
                ·
                  rfl

theorem cell20_628003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_628003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628003 prefixEnd_628003 := by exact prefixLift 628003
  have htrace : WordTrace (prefixWord ++ tailWord_628003) baseStart_628003 baseEnd_628003 := by
    simpa [prefixWord, tailWord_628003, baseEnd_628003] using wordTrace_append hprefix tailTrace_628003
  have hstable : (prefixWord ++ tailWord_628003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628003).length < 2 ^ (prefixWord ++ tailWord_628003).sum := by decide
  have hdescent : baseEnd_628003 < baseStart_628003 := by decide
  rcases family_descends (prefixWord ++ tailWord_628003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628030 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_628030 : Nat := 118140960795 + 628030 * 2 ^ 59
def prefixEnd_628030 : Nat := 4983230072969 + 3 ^ 40 * 628030 * 2
def baseEnd_628030 : Nat := 286650004838473834165999

theorem tailTrace_628030 : CollatzResearch.WordTrace tailWord_628030 prefixEnd_628030 286650004838473834165999 := by
  unfold tailWord_628030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863266989345255478723193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15270757276508029219857029 2863266989345255478723193)
  ·
    refine ⟨2147450242008941609042395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2863266989345255478723193 2147450242008941609042395)
    ·
      refine ⟨3221175363013412413563593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147450242008941609042395 3221175363013412413563593)
      ·
        refine ⟨2415881522260059310172695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3221175363013412413563593 2415881522260059310172695)
        ·
          refine ⟨3623822283390088965259043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415881522260059310172695 3623822283390088965259043)
          ·
            refine ⟨5435733425085133447888565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623822283390088965259043 5435733425085133447888565)
            ·
              refine ⟨509600008601731260739553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5435733425085133447888565 509600008601731260739553)
              ·
                refine ⟨382200006451298445554665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509600008601731260739553 382200006451298445554665)
                ·
                  refine ⟨286650004838473834165999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382200006451298445554665 286650004838473834165999)
                  ·
                    rfl

theorem cell20_628030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_628030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628030 prefixEnd_628030 := by exact prefixLift 628030
  have htrace : WordTrace (prefixWord ++ tailWord_628030) baseStart_628030 baseEnd_628030 := by
    simpa [prefixWord, tailWord_628030, baseEnd_628030] using wordTrace_append hprefix tailTrace_628030
  have hstable : (prefixWord ++ tailWord_628030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628030).length < 2 ^ (prefixWord ++ tailWord_628030).sum := by decide
  have hdescent : baseEnd_628030 < baseStart_628030 := by decide
  rcases family_descends (prefixWord ++ tailWord_628030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628044 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_628044 : Nat := 118140960795 + 628044 * 2 ^ 59
def prefixEnd_628044 : Nat := 4983230072969 + 3 ^ 40 * 628044 * 2
def baseEnd_628044 : Nat := 286656394819952007699275

theorem tailTrace_628044 : CollatzResearch.WordTrace tailWord_628044 prefixEnd_628044 286656394819952007699275 := by
  unfold tailWord_628044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453323268355662110397593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15271097691140882813863457 11453323268355662110397593)
  ·
    refine ⟨8589992451266746582798195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11453323268355662110397593 8589992451266746582798195)
    ·
      refine ⟨12884988676900119874197293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8589992451266746582798195 12884988676900119874197293)
      ·
        refine ⟨4831870753837544952823985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12884988676900119874197293 4831870753837544952823985)
        ·
          refine ⟨3623903065378158714617989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4831870753837544952823985 3623903065378158714617989)
          ·
            refine ⟨679481824758404758990873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3623903065378158714617989 679481824758404758990873)
            ·
              refine ⟨509611368568803569243155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679481824758404758990873 509611368568803569243155)
              ·
                refine ⟨764417052853205353864733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509611368568803569243155 764417052853205353864733)
                ·
                  refine ⟨286656394819952007699275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764417052853205353864733 286656394819952007699275)
                  ·
                    rfl

theorem cell20_628044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_628044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628044 prefixEnd_628044 := by exact prefixLift 628044
  have htrace : WordTrace (prefixWord ++ tailWord_628044) baseStart_628044 baseEnd_628044 := by
    simpa [prefixWord, tailWord_628044, baseEnd_628044] using wordTrace_append hprefix tailTrace_628044
  have hstable : (prefixWord ++ tailWord_628044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628044).length < 2 ^ (prefixWord ++ tailWord_628044).sum := by decide
  have hdescent : baseEnd_628044 < baseStart_628044 := by decide
  rcases family_descends (prefixWord ++ tailWord_628044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628048 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_628048 : Nat := 118140960795 + 628048 * 2 ^ 59
def prefixEnd_628048 : Nat := 4983230072969 + 3 ^ 40 * 628048 * 2
def baseEnd_628048 : Nat := 286658220528945771565925

theorem tailTrace_628048 : CollatzResearch.WordTrace tailWord_628048 prefixEnd_628048 286658220528945771565925 := by
  unfold tailWord_628048
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453396214348416451970399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15271194952464555269293865 11453396214348416451970399)
  ·
    refine ⟨17180094321522624677955599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11453396214348416451970399 17180094321522624677955599)
    ·
      refine ⟨25770141482283937016933399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17180094321522624677955599 25770141482283937016933399)
      ·
        refine ⟨38655212223425905525400099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25770141482283937016933399 38655212223425905525400099)
        ·
          refine ⟨57982818335138858288100149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38655212223425905525400099 57982818335138858288100149)
          ·
            refine ⟨5435889218919267964509389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57982818335138858288100149 5435889218919267964509389)
            ·
              refine ⟨2038458457094725486691021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5435889218919267964509389 2038458457094725486691021)
              ·
                refine ⟨764421921410522057509133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2038458457094725486691021 764421921410522057509133)
                ·
                  refine ⟨286658220528945771565925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764421921410522057509133 286658220528945771565925)
                  ·
                    rfl

theorem cell20_628048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_628048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628048 prefixEnd_628048 := by exact prefixLift 628048
  have htrace : WordTrace (prefixWord ++ tailWord_628048) baseStart_628048 baseEnd_628048 := by
    simpa [prefixWord, tailWord_628048, baseEnd_628048] using wordTrace_append hprefix tailTrace_628048
  have hstable : (prefixWord ++ tailWord_628048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628048).length < 2 ^ (prefixWord ++ tailWord_628048).sum := by decide
  have hdescent : baseEnd_628048 < baseStart_628048 := by decide
  rcases family_descends (prefixWord ++ tailWord_628048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628085 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 2]
def baseStart_628085 : Nat := 118140960795 + 628085 * 2 ^ 59
def prefixEnd_628085 : Nat := 4983230072969 + 3 ^ 40 * 628085 * 2
def baseEnd_628085 : Nat := 286675108337138087332441

theorem tailTrace_628085 : CollatzResearch.WordTrace tailWord_628085 prefixEnd_628085 286675108337138087332441 := by
  unfold tailWord_628085
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908141929562788223037709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15272094619708525482025139 22908141929562788223037709)
  ·
    refine ⟨8590553223586045583639141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22908141929562788223037709 8590553223586045583639141)
    ·
      refine ⟨1610728729422383546932339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8590553223586045583639141 1610728729422383546932339)
      ·
        refine ⟨2416093094133575320398509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610728729422383546932339 2416093094133575320398509)
        ·
          refine ⟨906034910300090745149441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2416093094133575320398509 906034910300090745149441)
          ·
            refine ⟨679526182725068058862081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906034910300090745149441 679526182725068058862081)
            ·
              refine ⟨509644637043801044146561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679526182725068058862081 509644637043801044146561)
              ·
                refine ⟨382233477782850783109921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509644637043801044146561 382233477782850783109921)
                ·
                  refine ⟨286675108337138087332441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382233477782850783109921 286675108337138087332441)
                  ·
                    rfl

theorem cell20_628085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_628085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628085 prefixEnd_628085 := by exact prefixLift 628085
  have htrace : WordTrace (prefixWord ++ tailWord_628085) baseStart_628085 baseEnd_628085 := by
    simpa [prefixWord, tailWord_628085, baseEnd_628085] using wordTrace_append hprefix tailTrace_628085
  have hstable : (prefixWord ++ tailWord_628085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628085).length < 2 ^ (prefixWord ++ tailWord_628085).sum := by decide
  have hdescent : baseEnd_628085 < baseStart_628085 := by decide
  rcases family_descends (prefixWord ++ tailWord_628085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628089 : List Nat := [1, 2, 1, 3, 2, 1, 6, 2, 2]
def baseStart_628089 : Nat := 118140960795 + 628089 * 2 ^ 59
def prefixEnd_628089 : Nat := 4983230072969 + 3 ^ 40 * 628089 * 2
def baseEnd_628089 : Nat := 286676934046131851199091

theorem tailTrace_628089 : CollatzResearch.WordTrace tailWord_628089 prefixEnd_628089 286676934046131851199091 := by
  unfold tailWord_628089
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908287821548296906183321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15272191881032197937455547 22908287821548296906183321)
  ·
    refine ⟨17181215866161222679637491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22908287821548296906183321 17181215866161222679637491)
    ·
      refine ⟨25771823799241834019456237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17181215866161222679637491 25771823799241834019456237)
      ·
        refine ⟨9664433924715687757296089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25771823799241834019456237 9664433924715687757296089)
        ·
          refine ⟨7248325443536765817972067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9664433924715687757296089 7248325443536765817972067)
          ·
            refine ⟨10872488165305148726958101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248325443536765817972067 10872488165305148726958101)
            ·
              refine ⟨509647882748678846576161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10872488165305148726958101 509647882748678846576161)
              ·
                refine ⟨382235912061509134932121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509647882748678846576161 382235912061509134932121)
                ·
                  refine ⟨286676934046131851199091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382235912061509134932121 286676934046131851199091)
                  ·
                    rfl

theorem cell20_628089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_628089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628089 prefixEnd_628089 := by exact prefixLift 628089
  have htrace : WordTrace (prefixWord ++ tailWord_628089) baseStart_628089 baseEnd_628089 := by
    simpa [prefixWord, tailWord_628089, baseEnd_628089] using wordTrace_append hprefix tailTrace_628089
  have hstable : (prefixWord ++ tailWord_628089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628089).length < 2 ^ (prefixWord ++ tailWord_628089).sum := by decide
  have hdescent : baseEnd_628089 < baseStart_628089 := by decide
  rcases family_descends (prefixWord ++ tailWord_628089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628093 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_628093 : Nat := 118140960795 + 628093 * 2 ^ 59
def prefixEnd_628093 : Nat := 4983230072969 + 3 ^ 40 * 628093 * 2
def baseEnd_628093 : Nat := 286678759755125615065741

theorem tailTrace_628093 : CollatzResearch.WordTrace tailWord_628093 prefixEnd_628093 286678759755125615065741 := by
  unfold tailWord_628093
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908433713533805589328933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15272289142355870392885955 22908433713533805589328933)
  ·
    refine ⟨4295331321287588547999175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22908433713533805589328933 4295331321287588547999175)
    ·
      refine ⟨6442996981931382821998763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295331321287588547999175 6442996981931382821998763)
      ·
        refine ⟨9664495472897074232998145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442996981931382821998763 9664495472897074232998145)
        ·
          refine ⟨7248371604672805674748609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9664495472897074232998145 7248371604672805674748609)
          ·
            refine ⟨5436278703504604256061457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7248371604672805674748609 5436278703504604256061457)
            ·
              refine ⟨4077209027628453192046093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5436278703504604256061457 4077209027628453192046093)
              ·
                refine ⟨1528953385360669947017285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4077209027628453192046093 1528953385360669947017285)
                ·
                  refine ⟨286678759755125615065741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528953385360669947017285 286678759755125615065741)
                  ·
                    rfl

theorem cell20_628093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_628093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628093 prefixEnd_628093 := by exact prefixLift 628093
  have htrace : WordTrace (prefixWord ++ tailWord_628093) baseStart_628093 baseEnd_628093 := by
    simpa [prefixWord, tailWord_628093, baseEnd_628093] using wordTrace_append hprefix tailTrace_628093
  have hstable : (prefixWord ++ tailWord_628093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628093).length < 2 ^ (prefixWord ++ tailWord_628093).sum := by decide
  have hdescent : baseEnd_628093 < baseStart_628093 := by decide
  rcases family_descends (prefixWord ++ tailWord_628093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628127 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 2]
def baseStart_628127 : Nat := 118140960795 + 628127 * 2 ^ 59
def prefixEnd_628127 : Nat := 4983230072969 + 3 ^ 40 * 628127 * 2
def baseEnd_628127 : Nat := 286694278281572607932269

theorem tailTrace_628127 : CollatzResearch.WordTrace tailWord_628127 prefixEnd_628127 286694278281572607932269 := by
  unfold tailWord_628127
  simp only [CollatzResearch.WordTrace]
  refine ⟨22909673795410629396066635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15273115863607086264044423 22909673795410629396066635)
  ·
    refine ⟨34364510693115944094099953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22909673795410629396066635 34364510693115944094099953)
    ·
      refine ⟨25773383019836958070574965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34364510693115944094099953 25773383019836958070574965)
      ·
        refine ⟨2416254658109714819116403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25773383019836958070574965 2416254658109714819116403)
        ·
          refine ⟨3624381987164572228674605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416254658109714819116403 3624381987164572228674605)
          ·
            refine ⟨1359143245186714585752977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3624381987164572228674605 1359143245186714585752977)
            ·
              refine ⟨1019357433890035939314733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359143245186714585752977 1019357433890035939314733)
              ·
                refine ⟨382259037708763477243025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019357433890035939314733 382259037708763477243025)
                ·
                  refine ⟨286694278281572607932269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382259037708763477243025 286694278281572607932269)
                  ·
                    rfl

theorem cell20_628127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2].length) (baseStart_628127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628127 prefixEnd_628127 := by exact prefixLift 628127
  have htrace : WordTrace (prefixWord ++ tailWord_628127) baseStart_628127 baseEnd_628127 := by
    simpa [prefixWord, tailWord_628127, baseEnd_628127] using wordTrace_append hprefix tailTrace_628127
  have hstable : (prefixWord ++ tailWord_628127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628127).length < 2 ^ (prefixWord ++ tailWord_628127).sum := by decide
  have hdescent : baseEnd_628127 < baseStart_628127 := by decide
  rcases family_descends (prefixWord ++ tailWord_628127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628141 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_628141 : Nat := 118140960795 + 628141 * 2 ^ 59
def prefixEnd_628141 : Nat := 4983230072969 + 3 ^ 40 * 628141 * 2
def baseEnd_628141 : Nat := 286700668263050781465545

theorem tailTrace_628141 : CollatzResearch.WordTrace tailWord_628141 prefixEnd_628141 286700668263050781465545 := by
  unfold tailWord_628141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22910184417359909787076277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15273456278239939858050851 22910184417359909787076277)
  ·
    refine ⟨2147829789127491542538401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22910184417359909787076277 2147829789127491542538401)
    ·
      refine ⟨1610872341845618656903801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2147829789127491542538401 1610872341845618656903801)
      ·
        refine ⟨1208154256384213992677851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1610872341845618656903801 1208154256384213992677851)
        ·
          refine ⟨1812231384576320989016777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208154256384213992677851 1812231384576320989016777)
          ·
            refine ⟨1359173538432240741762583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812231384576320989016777 1359173538432240741762583)
            ·
              refine ⟨2038760307648361112643875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359173538432240741762583 2038760307648361112643875)
              ·
                refine ⟨3058140461472541668965813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038760307648361112643875 3058140461472541668965813)
                ·
                  refine ⟨286700668263050781465545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3058140461472541668965813 286700668263050781465545)
                  ·
                    rfl

theorem cell20_628141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_628141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628141 prefixEnd_628141 := by exact prefixLift 628141
  have htrace : WordTrace (prefixWord ++ tailWord_628141) baseStart_628141 baseEnd_628141 := by
    simpa [prefixWord, tailWord_628141, baseEnd_628141] using wordTrace_append hprefix tailTrace_628141
  have hstable : (prefixWord ++ tailWord_628141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628141).length < 2 ^ (prefixWord ++ tailWord_628141).sum := by decide
  have hdescent : baseEnd_628141 < baseStart_628141 := by decide
  rcases family_descends (prefixWord ++ tailWord_628141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628172 : List Nat := [2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_628172 : Nat := 118140960795 + 628172 * 2 ^ 59
def prefixEnd_628172 : Nat := 4983230072969 + 3 ^ 40 * 628172 * 2
def baseEnd_628172 : Nat := 95571605835917483810695

theorem tailTrace_628172 : CollatzResearch.WordTrace tailWord_628172 prefixEnd_628172 95571605835917483810695 := by
  unfold tailWord_628172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11455657540123801040727385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15274210053498401387636513 11455657540123801040727385)
  ·
    refine ⟨8591743155092850780545539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11455657540123801040727385 8591743155092850780545539)
    ·
      refine ⟨12887614732639276170818309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8591743155092850780545539 12887614732639276170818309)
      ·
        refine ⟨2416427762369864282028433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12887614732639276170818309 2416427762369864282028433)
        ·
          refine ⟨1812320821777398211521325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2416427762369864282028433 1812320821777398211521325)
          ·
            refine ⟨679620308166524329320497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1812320821777398211521325 679620308166524329320497)
            ·
              refine ⟨509715231124893246990373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679620308166524329320497 509715231124893246990373)
              ·
                refine ⟨95571605835917483810695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509715231124893246990373 95571605835917483810695)
                ·
                  rfl

theorem cell20_628172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_628172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628172 prefixEnd_628172 := by exact prefixLift 628172
  have htrace : WordTrace (prefixWord ++ tailWord_628172) baseStart_628172 baseEnd_628172 := by
    simpa [prefixWord, tailWord_628172, baseEnd_628172] using wordTrace_append hprefix tailTrace_628172
  have hstable : (prefixWord ++ tailWord_628172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628172).length < 2 ^ (prefixWord ++ tailWord_628172).sum := by decide
  have hdescent : baseEnd_628172 < baseStart_628172 := by decide
  rcases family_descends (prefixWord ++ tailWord_628172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628182 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_628182 : Nat := 118140960795 + 628182 * 2 ^ 59
def prefixEnd_628182 : Nat := 4983230072969 + 3 ^ 40 * 628182 * 2
def baseEnd_628182 : Nat := 286719381780236861098711

theorem tailTrace_628182 : CollatzResearch.WordTrace tailWord_628182 prefixEnd_628182 286719381780236861098711 := by
  unfold tailWord_628182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431979988138210861832425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15274453206807582526212533 1431979988138210861832425)
  ·
    refine ⟨1073984991103658146374319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1431979988138210861832425 1073984991103658146374319)
    ·
      refine ⟨1610977486655487219561479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073984991103658146374319 1610977486655487219561479)
      ·
        refine ⟨2416466229983230829342219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610977486655487219561479 2416466229983230829342219)
        ·
          refine ⟨3624699344974846244013329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416466229983230829342219 3624699344974846244013329)
          ·
            refine ⟨2718524508731134683009997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624699344974846244013329 2718524508731134683009997)
            ·
              refine ⟨1019446690774175506128749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2718524508731134683009997 1019446690774175506128749)
              ·
                refine ⟨382292509040315814798281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019446690774175506128749 382292509040315814798281)
                ·
                  refine ⟨286719381780236861098711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382292509040315814798281 286719381780236861098711)
                  ·
                    rfl

theorem cell20_628182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_628182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628182 prefixEnd_628182 := by exact prefixLift 628182
  have htrace : WordTrace (prefixWord ++ tailWord_628182) baseStart_628182 baseEnd_628182 := by
    simpa [prefixWord, tailWord_628182, baseEnd_628182] using wordTrace_append hprefix tailTrace_628182
  have hstable : (prefixWord ++ tailWord_628182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628182).length < 2 ^ (prefixWord ++ tailWord_628182).sum := by decide
  have hdescent : baseEnd_628182 < baseStart_628182 := by decide
  rcases family_descends (prefixWord ++ tailWord_628182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628200 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_628200 : Nat := 118140960795 + 628200 * 2 ^ 59
def prefixEnd_628200 : Nat := 4983230072969 + 3 ^ 40 * 628200 * 2
def baseEnd_628200 : Nat := 286727597470708798498637

theorem tailTrace_628200 : CollatzResearch.WordTrace tailWord_628200 prefixEnd_628200 286727597470708798498637 := by
  unfold tailWord_628200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456168162073081431737027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15274890882764108575649369 11456168162073081431737027)
  ·
    refine ⟨17184252243109622147605541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11456168162073081431737027 17184252243109622147605541)
    ·
      refine ⟨3222047295583054152676039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17184252243109622147605541 3222047295583054152676039)
      ·
        refine ⟨4833070943374581229014059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222047295583054152676039 4833070943374581229014059)
        ·
          refine ⟨7249606415061871843521089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833070943374581229014059 7249606415061871843521089)
          ·
            refine ⟨5437204811296403882640817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7249606415061871843521089 5437204811296403882640817)
            ·
              refine ⟨4077903608472302911980613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437204811296403882640817 4077903608472302911980613)
              ·
                refine ⟨764606926588556795996365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4077903608472302911980613 764606926588556795996365)
                ·
                  refine ⟨286727597470708798498637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764606926588556795996365 286727597470708798498637)
                  ·
                    rfl

theorem cell20_628200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_628200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628200 prefixEnd_628200 := by exact prefixLift 628200
  have htrace : WordTrace (prefixWord ++ tailWord_628200) baseStart_628200 baseEnd_628200 := by
    simpa [prefixWord, tailWord_628200, baseEnd_628200] using wordTrace_append hprefix tailTrace_628200
  have hstable : (prefixWord ++ tailWord_628200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628200).length < 2 ^ (prefixWord ++ tailWord_628200).sum := by decide
  have hdescent : baseEnd_628200 < baseStart_628200 := by decide
  rcases family_descends (prefixWord ++ tailWord_628200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628207 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_628207 : Nat := 118140960795 + 628207 * 2 ^ 59
def prefixEnd_628207 : Nat := 4983230072969 + 3 ^ 40 * 628207 * 2
def baseEnd_628207 : Nat := 286730792461447885265275

theorem tailTrace_628207 : CollatzResearch.WordTrace tailWord_628207 prefixEnd_628207 286730792461447885265275 := by
  unfold tailWord_628207
  simp only [CollatzResearch.WordTrace]
  refine ⟨22912591635120803058978875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15275061090080535372652583 22912591635120803058978875)
  ·
    refine ⟨34368887452681204588468313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22912591635120803058978875 34368887452681204588468313)
    ·
      refine ⟨25776665589510903441351235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34368887452681204588468313 25776665589510903441351235)
      ·
        refine ⟨38664998384266355162026853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25776665589510903441351235 38664998384266355162026853)
        ·
          refine ⟨7249687197049941592880035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38664998384266355162026853 7249687197049941592880035)
          ·
            refine ⟨10874530795574912389320053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249687197049941592880035 10874530795574912389320053)
            ·
              refine ⟨1019487262085148036498755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10874530795574912389320053 1019487262085148036498755)
              ·
                refine ⟨1529230893127722054748133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019487262085148036498755 1529230893127722054748133)
                ·
                  refine ⟨286730792461447885265275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529230893127722054748133 286730792461447885265275)
                  ·
                    rfl

theorem cell20_628207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_628207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628207 prefixEnd_628207 := by exact prefixLift 628207
  have htrace : WordTrace (prefixWord ++ tailWord_628207) baseStart_628207 baseEnd_628207 := by
    simpa [prefixWord, tailWord_628207, baseEnd_628207] using wordTrace_append hprefix tailTrace_628207
  have hstable : (prefixWord ++ tailWord_628207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628207).length < 2 ^ (prefixWord ++ tailWord_628207).sum := by decide
  have hdescent : baseEnd_628207 < baseStart_628207 := by decide
  rcases family_descends (prefixWord ++ tailWord_628207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628213 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 3]
def baseStart_628213 : Nat := 118140960795 + 628213 * 2 ^ 59
def prefixEnd_628213 : Nat := 4983230072969 + 3 ^ 40 * 628213 * 2
def baseEnd_628213 : Nat := 286733531024938531065251

theorem tailTrace_628213 : CollatzResearch.WordTrace tailWord_628213 prefixEnd_628213 286733531024938531065251 := by
  unfold tailWord_628213
  simp only [CollatzResearch.WordTrace]
  refine ⟨22912810473099066083697293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15275206982066044055798195 22912810473099066083697293)
  ·
    refine ⟨8592303927412149781386485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22912810473099066083697293 8592303927412149781386485)
    ·
      refine ⟨805528493194889042004983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8592303927412149781386485 805528493194889042004983)
      ·
        refine ⟨1208292739792333563007475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805528493194889042004983 1208292739792333563007475)
        ·
          refine ⟨1812439109688500344511213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208292739792333563007475 1812439109688500344511213)
          ·
            refine ⟨679664666133187629191705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1812439109688500344511213 679664666133187629191705)
            ·
              refine ⟨509748499599890721893779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679664666133187629191705 509748499599890721893779)
              ·
                refine ⟨764622749399836082840669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509748499599890721893779 764622749399836082840669)
                ·
                  refine ⟨286733531024938531065251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764622749399836082840669 286733531024938531065251)
                  ·
                    rfl

theorem cell20_628213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_628213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628213 prefixEnd_628213 := by exact prefixLift 628213
  have htrace : WordTrace (prefixWord ++ tailWord_628213) baseStart_628213 baseEnd_628213 := by
    simpa [prefixWord, tailWord_628213, baseEnd_628213] using wordTrace_append hprefix tailTrace_628213
  have hstable : (prefixWord ++ tailWord_628213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628213).length < 2 ^ (prefixWord ++ tailWord_628213).sum := by decide
  have hdescent : baseEnd_628213 < baseStart_628213 := by decide
  rcases family_descends (prefixWord ++ tailWord_628213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628254 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_628254 : Nat := 118140960795 + 628254 * 2 ^ 59
def prefixEnd_628254 : Nat := 4983230072969 + 3 ^ 40 * 628254 * 2
def baseEnd_628254 : Nat := 286752244542124610698417

theorem tailTrace_628254 : CollatzResearch.WordTrace tailWord_628254 prefixEnd_628254 286752244542124610698417 := by
  unfold tailWord_628254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864288233243816260742477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15276203910633686723959877 2864288233243816260742477)
  ·
    refine ⟨1074108087466431097778429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2864288233243816260742477 1074108087466431097778429)
    ·
      refine ⟨402790532799911661666911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1074108087466431097778429 402790532799911661666911)
      ·
        refine ⟨604185799199867492500367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402790532799911661666911 604185799199867492500367)
        ·
          refine ⟨906278698799801238750551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604185799199867492500367 906278698799801238750551)
          ·
            refine ⟨1359418048199701858125827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906278698799801238750551 1359418048199701858125827)
            ·
              refine ⟨2039127072299552787188741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359418048199701858125827 2039127072299552787188741)
              ·
                refine ⟨382336326056166147597889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2039127072299552787188741 382336326056166147597889)
                ·
                  refine ⟨286752244542124610698417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382336326056166147597889 286752244542124610698417)
                  ·
                    rfl

theorem cell20_628254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_628254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628254 prefixEnd_628254 := by exact prefixLift 628254
  have htrace : WordTrace (prefixWord ++ tailWord_628254) baseStart_628254 baseEnd_628254 := by
    simpa [prefixWord, tailWord_628254, baseEnd_628254] using wordTrace_append hprefix tailTrace_628254
  have hstable : (prefixWord ++ tailWord_628254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628254).length < 2 ^ (prefixWord ++ tailWord_628254).sum := by decide
  have hdescent : baseEnd_628254 < baseStart_628254 := by decide
  rcases family_descends (prefixWord ++ tailWord_628254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628300 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_628300 : Nat := 118140960795 + 628300 * 2 ^ 59
def prefixEnd_628300 : Nat := 4983230072969 + 3 ^ 40 * 628300 * 2
def baseEnd_628300 : Nat := 286773240195552895164895

theorem tailTrace_628300 : CollatzResearch.WordTrace tailWord_628300 prefixEnd_628300 286773240195552895164895 := by
  unfold tailWord_628300
  simp only [CollatzResearch.WordTrace]
  refine ⟨11457991811891939971057177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15277322415855919961409569 11457991811891939971057177)
  ·
    refine ⟨8593493858918954978292883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11457991811891939971057177 8593493858918954978292883)
    ·
      refine ⟨12890240788378432467439325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8593493858918954978292883 12890240788378432467439325)
      ·
        refine ⟨4833840295641912175289747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12890240788378432467439325 4833840295641912175289747)
        ·
          refine ⟨7250760443462868262934621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833840295641912175289747 7250760443462868262934621)
          ·
            refine ⟨2719035166298575598600483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7250760443462868262934621 2719035166298575598600483)
            ·
              refine ⟨4078552749447863397900725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719035166298575598600483 4078552749447863397900725)
              ·
                refine ⟨382364320260737193553193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4078552749447863397900725 382364320260737193553193)
                ·
                  refine ⟨286773240195552895164895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382364320260737193553193 286773240195552895164895)
                  ·
                    rfl

theorem cell20_628300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_628300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628300 prefixEnd_628300 := by exact prefixLift 628300
  have htrace : WordTrace (prefixWord ++ tailWord_628300) baseStart_628300 baseEnd_628300 := by
    simpa [prefixWord, tailWord_628300, baseEnd_628300] using wordTrace_append hprefix tailTrace_628300
  have hstable : (prefixWord ++ tailWord_628300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628300).length < 2 ^ (prefixWord ++ tailWord_628300).sum := by decide
  have hdescent : baseEnd_628300 < baseStart_628300 := by decide
  rcases family_descends (prefixWord ++ tailWord_628300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628304 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_628304 : Nat := 118140960795 + 628304 * 2 ^ 59
def prefixEnd_628304 : Nat := 4983230072969 + 3 ^ 40 * 628304 * 2
def baseEnd_628304 : Nat := 286775065904546659031545

theorem tailTrace_628304 : CollatzResearch.WordTrace tailWord_628304 prefixEnd_628304 286775065904546659031545 := by
  unfold tailWord_628304
  simp only [CollatzResearch.WordTrace]
  refine ⟨11458064757884694312629983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15277419677179592416839977 11458064757884694312629983)
  ·
    refine ⟨17187097136827041468944975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11458064757884694312629983 17187097136827041468944975)
    ·
      refine ⟨25780645705240562203417463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17187097136827041468944975 25780645705240562203417463)
      ·
        refine ⟨38670968557860843305126195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25780645705240562203417463 38670968557860843305126195)
        ·
          refine ⟨58006452836791264957689293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38670968557860843305126195 58006452836791264957689293)
          ·
            refine ⟨21752419813796724359133485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58006452836791264957689293 21752419813796724359133485)
            ·
              refine ⟨8157157430173771634675057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21752419813796724359133485 8157157430173771634675057)
              ·
                refine ⟨6117868072630328726006293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8157157430173771634675057 6117868072630328726006293)
                ·
                  refine ⟨286775065904546659031545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6117868072630328726006293 286775065904546659031545)
                  ·
                    rfl

theorem cell20_628304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_628304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628304 prefixEnd_628304 := by exact prefixLift 628304
  have htrace : WordTrace (prefixWord ++ tailWord_628304) baseStart_628304 baseEnd_628304 := by
    simpa [prefixWord, tailWord_628304, baseEnd_628304] using wordTrace_append hprefix tailTrace_628304
  have hstable : (prefixWord ++ tailWord_628304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628304).length < 2 ^ (prefixWord ++ tailWord_628304).sum := by decide
  have hdescent : baseEnd_628304 < baseStart_628304 := by decide
  rcases family_descends (prefixWord ++ tailWord_628304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628321 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_628321 : Nat := 118140960795 + 628321 * 2 ^ 59
def prefixEnd_628321 : Nat := 4983230072969 + 3 ^ 40 * 628321 * 2
def baseEnd_628321 : Nat := 286782825167770155464809

theorem tailTrace_628321 : CollatzResearch.WordTrace tailWord_628321 prefixEnd_628321 286782825167770155464809 := by
  unfold tailWord_628321
  simp only [CollatzResearch.WordTrace]
  refine ⟨22916749556707800528628817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15277833037805200352419211 22916749556707800528628817)
  ·
    refine ⟨17187562167530850396471613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22916749556707800528628817 17187562167530850396471613)
    ·
      refine ⟨6445335812824068898676855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17187562167530850396471613 6445335812824068898676855)
      ·
        refine ⟨9668003719236103348015283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6445335812824068898676855 9668003719236103348015283)
        ·
          refine ⟨14502005578854155022022925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9668003719236103348015283 14502005578854155022022925)
          ·
            refine ⟨5438252092070308133258597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14502005578854155022022925 5438252092070308133258597)
            ·
              refine ⟨1019672267263182774985987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5438252092070308133258597 1019672267263182774985987)
              ·
                refine ⟨1529508400894774162478981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019672267263182774985987 1529508400894774162478981)
                ·
                  refine ⟨286782825167770155464809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529508400894774162478981 286782825167770155464809)
                  ·
                    rfl

theorem cell20_628321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_628321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628321 prefixEnd_628321 := by exact prefixLift 628321
  have htrace : WordTrace (prefixWord ++ tailWord_628321) baseStart_628321 baseEnd_628321 := by
    simpa [prefixWord, tailWord_628321, baseEnd_628321] using wordTrace_append hprefix tailTrace_628321
  have hstable : (prefixWord ++ tailWord_628321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628321).length < 2 ^ (prefixWord ++ tailWord_628321).sum := by decide
  have hdescent : baseEnd_628321 < baseStart_628321 := by decide
  rcases family_descends (prefixWord ++ tailWord_628321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628366 : List Nat := [4, 1, 1, 3, 1, 2, 8]
def baseStart_628366 : Nat := 118140960795 + 628366 * 2 ^ 59
def prefixEnd_628366 : Nat := 4983230072969 + 3 ^ 40 * 628366 * 2
def baseEnd_628366 : Nat := 31867040488216666551625

theorem tailTrace_628366 : CollatzResearch.WordTrace tailWord_628366 prefixEnd_628366 31867040488216666551625 := by
  unfold tailWord_628366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864798855193096651752119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15278927227696515476011301 2864798855193096651752119)
  ·
    refine ⟨4297198282789644977628179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864798855193096651752119 4297198282789644977628179)
    ·
      refine ⟨6445797424184467466442269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4297198282789644977628179 6445797424184467466442269)
      ·
        refine ⟨2417174034069175299915851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6445797424184467466442269 2417174034069175299915851)
        ·
          refine ⟨3625761051103762949873777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417174034069175299915851 3625761051103762949873777)
          ·
            refine ⟨2719320788327822212405333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625761051103762949873777 2719320788327822212405333)
            ·
              refine ⟨31867040488216666551625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2719320788327822212405333 31867040488216666551625)
              ·
                rfl

theorem cell20_628366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_628366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628366 prefixEnd_628366 := by exact prefixLift 628366
  have htrace : WordTrace (prefixWord ++ tailWord_628366) baseStart_628366 baseEnd_628366 := by
    simpa [prefixWord, tailWord_628366, baseEnd_628366] using wordTrace_append hprefix tailTrace_628366
  have hstable : (prefixWord ++ tailWord_628366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628366).length < 2 ^ (prefixWord ++ tailWord_628366).sum := by decide
  have hdescent : baseEnd_628366 < baseStart_628366 := by decide
  rcases family_descends (prefixWord ++ tailWord_628366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628372 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_628372 : Nat := 118140960795 + 628372 * 2 ^ 59
def prefixEnd_628372 : Nat := 4983230072969 + 3 ^ 40 * 628372 * 2
def baseEnd_628372 : Nat := 286806102957440644764601

theorem tailTrace_628372 : CollatzResearch.WordTrace tailWord_628372 prefixEnd_628372 286806102957440644764601 := by
  unfold tailWord_628372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459304839761518119367685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15279073119682024159156913 11459304839761518119367685)
  ·
    refine ⟨2148619657455284647381441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11459304839761518119367685 2148619657455284647381441)
    ·
      refine ⟨1611464743091463485536081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148619657455284647381441 1611464743091463485536081)
      ·
        refine ⟨1208598557318597614152061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611464743091463485536081 1208598557318597614152061)
        ·
          refine ⟨453224458994474105307023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1208598557318597614152061 453224458994474105307023)
          ·
            refine ⟨679836688491711157960535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453224458994474105307023 679836688491711157960535)
            ·
              refine ⟨1019755032737566736940803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679836688491711157960535 1019755032737566736940803)
              ·
                refine ⟨1529632549106350105411205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019755032737566736940803 1529632549106350105411205)
                ·
                  refine ⟨286806102957440644764601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529632549106350105411205 286806102957440644764601)
                  ·
                    rfl

theorem cell20_628372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_628372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628372 prefixEnd_628372 := by exact prefixLift 628372
  have htrace : WordTrace (prefixWord ++ tailWord_628372) baseStart_628372 baseEnd_628372 := by
    simpa [prefixWord, tailWord_628372, baseEnd_628372] using wordTrace_append hprefix tailTrace_628372
  have hstable : (prefixWord ++ tailWord_628372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628372).length < 2 ^ (prefixWord ++ tailWord_628372).sum := by decide
  have hdescent : baseEnd_628372 < baseStart_628372 := by decide
  rcases family_descends (prefixWord ++ tailWord_628372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628376 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_628376 : Nat := 118140960795 + 628376 * 2 ^ 59
def prefixEnd_628376 : Nat := 4983230072969 + 3 ^ 40 * 628376 * 2
def baseEnd_628376 : Nat := 286807928666434408631251

theorem tailTrace_628376 : CollatzResearch.WordTrace tailWord_628376 prefixEnd_628376 286807928666434408631251 := by
  unfold tailWord_628376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459377785754272460940491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15279170381005696614587321 11459377785754272460940491)
  ·
    refine ⟨17189066678631408691410737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11459377785754272460940491 17189066678631408691410737)
    ·
      refine ⟨12891800008973556518558053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17189066678631408691410737 12891800008973556518558053)
      ·
        refine ⟨2417212501682541847229635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12891800008973556518558053 2417212501682541847229635)
        ·
          refine ⟨3625818752523812770844453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417212501682541847229635 3625818752523812770844453)
          ·
            refine ⟨679841016098214894533335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3625818752523812770844453 679841016098214894533335)
            ·
              refine ⟨1019761524147322341800003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679841016098214894533335 1019761524147322341800003)
              ·
                refine ⟨1529642286220983512700005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019761524147322341800003 1529642286220983512700005)
                ·
                  refine ⟨286807928666434408631251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529642286220983512700005 286807928666434408631251)
                  ·
                    rfl

theorem cell20_628376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_628376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628376 prefixEnd_628376 := by exact prefixLift 628376
  have htrace : WordTrace (prefixWord ++ tailWord_628376) baseStart_628376 baseEnd_628376 := by
    simpa [prefixWord, tailWord_628376, baseEnd_628376] using wordTrace_append hprefix tailTrace_628376
  have hstable : (prefixWord ++ tailWord_628376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628376).length < 2 ^ (prefixWord ++ tailWord_628376).sum := by decide
  have hdescent : baseEnd_628376 < baseStart_628376 := by decide
  rcases family_descends (prefixWord ++ tailWord_628376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628386 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_628386 : Nat := 118140960795 + 628386 * 2 ^ 59
def prefixEnd_628386 : Nat := 4983230072969 + 3 ^ 40 * 628386 * 2
def baseEnd_628386 : Nat := 286812492938918818297877

theorem tailTrace_628386 : CollatzResearch.WordTrace tailWord_628386 prefixEnd_628386 286812492938918818297877 := by
  unfold tailWord_628386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5729780075368079157436253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15279413534314877753163341 5729780075368079157436253)
  ·
    refine ⟨2148667528263029684038595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5729780075368079157436253 2148667528263029684038595)
    ·
      refine ⟨3223001292394544526057893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148667528263029684038595 3223001292394544526057893)
      ·
        refine ⟨604312742323977098635855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3223001292394544526057893 604312742323977098635855)
        ·
          refine ⟨906469113485965647953783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604312742323977098635855 906469113485965647953783)
          ·
            refine ⟨1359703670228948471930675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906469113485965647953783 1359703670228948471930675)
            ·
              refine ⟨2039555505343422707896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359703670228948471930675 2039555505343422707896013)
              ·
                refine ⟨764833314503783515461005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2039555505343422707896013 764833314503783515461005)
                ·
                  refine ⟨286812492938918818297877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764833314503783515461005 286812492938918818297877)
                  ·
                    rfl

theorem cell20_628386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_628386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628386 prefixEnd_628386 := by exact prefixLift 628386
  have htrace : WordTrace (prefixWord ++ tailWord_628386) baseStart_628386 baseEnd_628386 := by
    simpa [prefixWord, tailWord_628386, baseEnd_628386] using wordTrace_append hprefix tailTrace_628386
  have hstable : (prefixWord ++ tailWord_628386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628386).length < 2 ^ (prefixWord ++ tailWord_628386).sum := by decide
  have hdescent : baseEnd_628386 < baseStart_628386 := by decide
  rcases family_descends (prefixWord ++ tailWord_628386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628397 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_628397 : Nat := 118140960795 + 628397 * 2 ^ 59
def prefixEnd_628397 : Nat := 4983230072969 + 3 ^ 40 * 628397 * 2
def baseEnd_628397 : Nat := 286817513638651668931165

theorem tailTrace_628397 : CollatzResearch.WordTrace tailWord_628397 prefixEnd_628397 286817513638651668931165 := by
  unfold tailWord_628397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22919521504432465508395445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15279681002954977005596963 22919521504432465508395445)
  ·
    refine ⟨2148705141040543641412073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22919521504432465508395445 2148705141040543641412073)
    ·
      refine ⟨1611528855780407731059055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148705141040543641412073 1611528855780407731059055)
      ·
        refine ⟨2417293283670611596588583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611528855780407731059055 2417293283670611596588583)
        ·
          refine ⟨3625939925505917394882875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417293283670611596588583 3625939925505917394882875)
          ·
            refine ⟨5438909888258876092324313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625939925505917394882875 5438909888258876092324313)
            ·
              refine ⟨4079182416194157069243235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5438909888258876092324313 4079182416194157069243235)
              ·
                refine ⟨6118773624291235603864853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079182416194157069243235 6118773624291235603864853)
                ·
                  refine ⟨286817513638651668931165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6118773624291235603864853 286817513638651668931165)
                  ·
                    rfl

theorem cell20_628397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_628397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628397 prefixEnd_628397 := by exact prefixLift 628397
  have htrace : WordTrace (prefixWord ++ tailWord_628397) baseStart_628397 baseEnd_628397 := by
    simpa [prefixWord, tailWord_628397, baseEnd_628397] using wordTrace_append hprefix tailTrace_628397
  have hstable : (prefixWord ++ tailWord_628397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628397).length < 2 ^ (prefixWord ++ tailWord_628397).sum := by decide
  have hdescent : baseEnd_628397 < baseStart_628397 := by decide
  rcases family_descends (prefixWord ++ tailWord_628397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628442 : List Nat := [3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_628442 : Nat := 118140960795 + 628442 * 2 ^ 59
def prefixEnd_628442 : Nat := 4983230072969 + 3 ^ 40 * 628442 * 2
def baseEnd_628442 : Nat := 95612684288277170810327

theorem tailTrace_628442 : CollatzResearch.WordTrace tailWord_628442 prefixEnd_628442 95612684288277170810327 := by
  unfold tailWord_628442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730290697317359548445895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15280775192846292129189053 5730290697317359548445895)
  ·
    refine ⟨8595436045976039322668843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730290697317359548445895 8595436045976039322668843)
    ·
      refine ⟨12893154068964058984003265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595436045976039322668843 12893154068964058984003265)
      ·
        refine ⟨9669865551723044238002449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12893154068964058984003265 9669865551723044238002449)
        ·
          refine ⟨7252399163792283178501837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9669865551723044238002449 7252399163792283178501837)
          ·
            refine ⟨2719649686422106191938189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7252399163792283178501837 2719649686422106191938189)
            ·
              refine ⟨1019868632408289821976821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2719649686422106191938189 1019868632408289821976821)
              ·
                refine ⟨95612684288277170810327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1019868632408289821976821 95612684288277170810327)
                ·
                  rfl

theorem cell20_628442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_628442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628442 prefixEnd_628442 := by exact prefixLift 628442
  have htrace : WordTrace (prefixWord ++ tailWord_628442) baseStart_628442 baseEnd_628442 := by
    simpa [prefixWord, tailWord_628442, baseEnd_628442] using wordTrace_append hprefix tailTrace_628442
  have hstable : (prefixWord ++ tailWord_628442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628442).length < 2 ^ (prefixWord ++ tailWord_628442).sum := by decide
  have hdescent : baseEnd_628442 < baseStart_628442 := by decide
  rcases family_descends (prefixWord ++ tailWord_628442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628490 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_628490 : Nat := 118140960795 + 628490 * 2 ^ 59
def prefixEnd_628490 : Nat := 4983230072969 + 3 ^ 40 * 628490 * 2
def baseEnd_628490 : Nat := 286859961372756678830785

theorem tailTrace_628490 : CollatzResearch.WordTrace tailWord_628490 prefixEnd_628490 286859961372756678830785 := by
  unfold tailWord_628490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730728373273885597882731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15281942328730361594353949 5730728373273885597882731)
  ·
    refine ⟨8596092559910828396824097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730728373273885597882731 8596092559910828396824097)
    ·
      refine ⟨6447069419933121297618073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8596092559910828396824097 6447069419933121297618073)
      ·
        refine ⟨4835302064949840973213555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6447069419933121297618073 4835302064949840973213555)
        ·
          refine ⟨7252953097424761459820333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835302064949840973213555 7252953097424761459820333)
          ·
            refine ⟨2719857411534285547432625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7252953097424761459820333 2719857411534285547432625)
            ·
              refine ⟨2039893058650714160574469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2719857411534285547432625 2039893058650714160574469)
              ·
                refine ⟨382479948497008905107713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2039893058650714160574469 382479948497008905107713)
                ·
                  refine ⟨286859961372756678830785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382479948497008905107713 286859961372756678830785)
                  ·
                    rfl

theorem cell20_628490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_628490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628490 prefixEnd_628490 := by exact prefixLift 628490
  have htrace : WordTrace (prefixWord ++ tailWord_628490) baseStart_628490 baseEnd_628490 := by
    simpa [prefixWord, tailWord_628490, baseEnd_628490] using wordTrace_append hprefix tailTrace_628490
  have hstable : (prefixWord ++ tailWord_628490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628490).length < 2 ^ (prefixWord ++ tailWord_628490).sum := by decide
  have hdescent : baseEnd_628490 < baseStart_628490 := by decide
  rcases family_descends (prefixWord ++ tailWord_628490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628510 : List Nat := [4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_628510 : Nat := 118140960795 + 628510 * 2 ^ 59
def prefixEnd_628510 : Nat := 4983230072969 + 3 ^ 40 * 628510 * 2
def baseEnd_628510 : Nat := 95623029972575166054679

theorem tailTrace_628510 : CollatzResearch.WordTrace tailWord_628510 prefixEnd_628510 95623029972575166054679 := by
  unfold tailWord_628510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865455369127885725907373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15282428635348723871505989 2865455369127885725907373)
  ·
    refine ⟨1074545763422957147215265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2865455369127885725907373 1074545763422957147215265)
    ·
      refine ⟨805909322567217860411449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074545763422957147215265 805909322567217860411449)
      ·
        refine ⟨604431991925413395308587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 805909322567217860411449 604431991925413395308587)
        ·
          refine ⟨906647987888120092962881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604431991925413395308587 906647987888120092962881)
          ·
            refine ⟨679985990916090069722161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906647987888120092962881 679985990916090069722161)
            ·
              refine ⟨509989493187067552291621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679985990916090069722161 509989493187067552291621)
              ·
                refine ⟨95623029972575166054679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509989493187067552291621 95623029972575166054679)
                ·
                  rfl

theorem cell20_628510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_628510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628510 prefixEnd_628510 := by exact prefixLift 628510
  have htrace : WordTrace (prefixWord ++ tailWord_628510) baseStart_628510 baseEnd_628510 := by
    simpa [prefixWord, tailWord_628510, baseEnd_628510] using wordTrace_append hprefix tailTrace_628510
  have hstable : (prefixWord ++ tailWord_628510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628510).length < 2 ^ (prefixWord ++ tailWord_628510).sum := by decide
  have hdescent : baseEnd_628510 < baseStart_628510 := by decide
  rcases family_descends (prefixWord ++ tailWord_628510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628542 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_628542 : Nat := 118140960795 + 628542 * 2 ^ 59
def prefixEnd_628542 : Nat := 4983230072969 + 3 ^ 40 * 628542 * 2
def baseEnd_628542 : Nat := 286883695589675609097239

theorem tailTrace_628542 : CollatzResearch.WordTrace tailWord_628542 prefixEnd_628542 286883695589675609097239 := by
  unfold tailWord_628542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865601261113394409052985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15283206725938103514949253 2865601261113394409052985)
  ·
    refine ⟨2149200945835045806789739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2865601261113394409052985 2149200945835045806789739)
    ·
      refine ⟨3223801418752568710184609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149200945835045806789739 3223801418752568710184609)
      ·
        refine ⟨2417851064064426532638457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223801418752568710184609 2417851064064426532638457)
        ·
          refine ⟨1813388298048319899478843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417851064064426532638457 1813388298048319899478843)
          ·
            refine ⟨2720082447072479849218265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813388298048319899478843 2720082447072479849218265)
            ·
              refine ⟨2040061835304359886913699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720082447072479849218265 2040061835304359886913699)
              ·
                refine ⟨3060092752956539830370549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040061835304359886913699 3060092752956539830370549)
                ·
                  refine ⟨286883695589675609097239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3060092752956539830370549 286883695589675609097239)
                  ·
                    rfl

theorem cell20_628542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_628542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628542 prefixEnd_628542 := by exact prefixLift 628542
  have htrace : WordTrace (prefixWord ++ tailWord_628542) baseStart_628542 baseEnd_628542 := by
    simpa [prefixWord, tailWord_628542, baseEnd_628542] using wordTrace_append hprefix tailTrace_628542
  have hstable : (prefixWord ++ tailWord_628542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628542).length < 2 ^ (prefixWord ++ tailWord_628542).sum := by decide
  have hdescent : baseEnd_628542 < baseStart_628542 := by decide
  rcases family_descends (prefixWord ++ tailWord_628542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628570 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_628570 : Nat := 118140960795 + 628570 * 2 ^ 59
def prefixEnd_628570 : Nat := 4983230072969 + 3 ^ 40 * 628570 * 2
def baseEnd_628570 : Nat := 286896475552631956163791

theorem tailTrace_628570 : CollatzResearch.WordTrace tailWord_628570 prefixEnd_628570 286896475552631956163791 := by
  unfold tailWord_628570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731457833201429013610791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15283887555203810702962109 5731457833201429013610791)
  ·
    refine ⟨8597186749802143520416187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5731457833201429013610791 8597186749802143520416187)
    ·
      refine ⟨12895780124703215280624281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597186749802143520416187 12895780124703215280624281)
      ·
        refine ⟨9671835093527411460468211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12895780124703215280624281 9671835093527411460468211)
        ·
          refine ⟨14507752640291117190702317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9671835093527411460468211 14507752640291117190702317)
          ·
            refine ⟨5440407240109168946513369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14507752640291117190702317 5440407240109168946513369)
            ·
              refine ⟨4080305430081876709885027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5440407240109168946513369 4080305430081876709885027)
              ·
                refine ⟨6120458145122815064827541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080305430081876709885027 6120458145122815064827541)
                ·
                  refine ⟨286896475552631956163791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6120458145122815064827541 286896475552631956163791)
                  ·
                    rfl

theorem cell20_628570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_628570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628570 prefixEnd_628570 := by exact prefixLift 628570
  have htrace : WordTrace (prefixWord ++ tailWord_628570) baseStart_628570 baseEnd_628570 := by
    simpa [prefixWord, tailWord_628570, baseEnd_628570] using wordTrace_append hprefix tailTrace_628570
  have hstable : (prefixWord ++ tailWord_628570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628570).length < 2 ^ (prefixWord ++ tailWord_628570).sum := by decide
  have hdescent : baseEnd_628570 < baseStart_628570 := by decide
  rcases family_descends (prefixWord ++ tailWord_628570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628577 : List Nat := [1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_628577 : Nat := 118140960795 + 628577 * 2 ^ 59
def prefixEnd_628577 : Nat := 4983230072969 + 3 ^ 40 * 628577 * 2
def baseEnd_628577 : Nat := 95633223514457014310143

theorem tailTrace_628577 : CollatzResearch.WordTrace tailWord_628577 prefixEnd_628577 95633223514457014310143 := by
  unfold tailWord_628577
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926086643780356249947985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15284057762520237499965323 22926086643780356249947985)
  ·
    refine ⟨17194564982835267187460989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22926086643780356249947985 17194564982835267187460989)
    ·
      refine ⟨6447961868563225195297871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17194564982835267187460989 6447961868563225195297871)
      ·
        refine ⟨9671942802844837792946807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6447961868563225195297871 9671942802844837792946807)
        ·
          refine ⟨14507914204267256689420211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9671942802844837792946807 14507914204267256689420211)
          ·
            refine ⟨21761871306400885034130317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14507914204267256689420211 21761871306400885034130317)
            ·
              refine ⟨8160701739900331887798869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21761871306400885034130317 8160701739900331887798869)
              ·
                refine ⟨95633223514457014310143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8160701739900331887798869 95633223514457014310143)
                ·
                  rfl

theorem cell20_628577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_628577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628577 prefixEnd_628577 := by exact prefixLift 628577
  have htrace : WordTrace (prefixWord ++ tailWord_628577) baseStart_628577 baseEnd_628577 := by
    simpa [prefixWord, tailWord_628577, baseEnd_628577] using wordTrace_append hprefix tailTrace_628577
  have hstable : (prefixWord ++ tailWord_628577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628577).length < 2 ^ (prefixWord ++ tailWord_628577).sum := by decide
  have hdescent : baseEnd_628577 < baseStart_628577 := by decide
  rcases family_descends (prefixWord ++ tailWord_628577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628587 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 2]
def baseStart_628587 : Nat := 118140960795 + 628587 * 2 ^ 59
def prefixEnd_628587 : Nat := 4983230072969 + 3 ^ 40 * 628587 * 2
def baseEnd_628587 : Nat := 286904234815855452597055

theorem tailTrace_628587 : CollatzResearch.WordTrace tailWord_628587 prefixEnd_628587 286904234815855452597055 := by
  unfold tailWord_628587
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926451373744127957812015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15284300915829418638541343 22926451373744127957812015)
  ·
    refine ⟨34389677060616191936718023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22926451373744127957812015 34389677060616191936718023)
    ·
      refine ⟨51584515590924287905077035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34389677060616191936718023 51584515590924287905077035)
      ·
        refine ⟨77376773386386431857615553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51584515590924287905077035 77376773386386431857615553)
        ·
          refine ⟨58032580039789823893211665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77376773386386431857615553 58032580039789823893211665)
          ·
            refine ⟨43524435029842367919908749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58032580039789823893211665 43524435029842367919908749)
            ·
              refine ⟨16321663136190887969965781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43524435029842367919908749 16321663136190887969965781)
              ·
                refine ⟨382538979754473936796073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16321663136190887969965781 382538979754473936796073)
                ·
                  refine ⟨286904234815855452597055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382538979754473936796073 286904234815855452597055)
                  ·
                    rfl

theorem cell20_628587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2].length) (baseStart_628587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628587 prefixEnd_628587 := by exact prefixLift 628587
  have htrace : WordTrace (prefixWord ++ tailWord_628587) baseStart_628587 baseEnd_628587 := by
    simpa [prefixWord, tailWord_628587, baseEnd_628587] using wordTrace_append hprefix tailTrace_628587
  have hstable : (prefixWord ++ tailWord_628587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628587).length < 2 ^ (prefixWord ++ tailWord_628587).sum := by decide
  have hdescent : baseEnd_628587 < baseStart_628587 := by decide
  rcases family_descends (prefixWord ++ tailWord_628587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628608 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_628608 : Nat := 118140960795 + 628608 * 2 ^ 59
def prefixEnd_628608 : Nat := 4983230072969 + 3 ^ 40 * 628608 * 2
def baseEnd_628608 : Nat := 286913819788072712896969

theorem tailTrace_628608 : CollatzResearch.WordTrace tailWord_628608 prefixEnd_628608 286913819788072712896969 := by
  unfold tailWord_628608
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463608653334024272163239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15284811537778699029550985 11463608653334024272163239)
  ·
    refine ⟨17195412980001036408244859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11463608653334024272163239 17195412980001036408244859)
    ·
      refine ⟨25793119470001554612367289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17195412980001036408244859 25793119470001554612367289)
      ·
        refine ⟨19344839602501165959275467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25793119470001554612367289 19344839602501165959275467)
        ·
          refine ⟨29017259403751748938913201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19344839602501165959275467 29017259403751748938913201)
          ·
            refine ⟨21762944552813811704184901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29017259403751748938913201 21762944552813811704184901)
            ·
              refine ⟨4080552103652589694534669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21762944552813811704184901 4080552103652589694534669)
              ·
                refine ⟨1530207038869721135450501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4080552103652589694534669 1530207038869721135450501)
                ·
                  refine ⟨286913819788072712896969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530207038869721135450501 286913819788072712896969)
                  ·
                    rfl

theorem cell20_628608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_628608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628608 prefixEnd_628608 := by exact prefixLift 628608
  have htrace : WordTrace (prefixWord ++ tailWord_628608) baseStart_628608 baseEnd_628608 := by
    simpa [prefixWord, tailWord_628608, baseEnd_628608] using wordTrace_append hprefix tailTrace_628608
  have hstable : (prefixWord ++ tailWord_628608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628608).length < 2 ^ (prefixWord ++ tailWord_628608).sum := by decide
  have hdescent : baseEnd_628608 < baseStart_628608 := by decide
  rcases family_descends (prefixWord ++ tailWord_628608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628697 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 2]
def baseStart_628697 : Nat := 118140960795 + 628697 * 2 ^ 59
def prefixEnd_628697 : Nat := 4983230072969 + 3 ^ 40 * 628697 * 2
def baseEnd_628697 : Nat := 286954441813183958929939

theorem tailTrace_628697 : CollatzResearch.WordTrace tailWord_628697 prefixEnd_628697 286954441813183958929939 := by
  unfold tailWord_628697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22930463403345616744316345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15286975602230411162877563 22930463403345616744316345)
  ·
    refine ⟨17197847552509212558237259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22930463403345616744316345 17197847552509212558237259)
    ·
      refine ⟨25796771328763818837355889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197847552509212558237259 25796771328763818837355889)
      ·
        refine ⟨19347578496572864128016917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25796771328763818837355889 19347578496572864128016917)
        ·
          refine ⟨906917742026853006000793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19347578496572864128016917 906917742026853006000793)
          ·
            refine ⟨680188306520139754500595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906917742026853006000793 680188306520139754500595)
            ·
              refine ⟨1020282459780209631750893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680188306520139754500595 1020282459780209631750893)
              ·
                refine ⟨382605922417578611906585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020282459780209631750893 382605922417578611906585)
                ·
                  refine ⟨286954441813183958929939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382605922417578611906585 286954441813183958929939)
                  ·
                    rfl

theorem cell20_628697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_628697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628697 prefixEnd_628697 := by exact prefixLift 628697
  have htrace : WordTrace (prefixWord ++ tailWord_628697) baseStart_628697 baseEnd_628697 := by
    simpa [prefixWord, tailWord_628697, baseEnd_628697] using wordTrace_append hprefix tailTrace_628697
  have hstable : (prefixWord ++ tailWord_628697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628697).length < 2 ^ (prefixWord ++ tailWord_628697).sum := by decide
  have hdescent : baseEnd_628697 < baseStart_628697 := by decide
  rcases family_descends (prefixWord ++ tailWord_628697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628718 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_628718 : Nat := 118140960795 + 628718 * 2 ^ 59
def prefixEnd_628718 : Nat := 4983230072969 + 3 ^ 40 * 628718 * 2
def baseEnd_628718 : Nat := 286964026785401219229853

theorem tailTrace_628718 : CollatzResearch.WordTrace tailWord_628718 prefixEnd_628718 286964026785401219229853 := by
  unfold tailWord_628718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866403667033692166353851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15287486224179691553887205 2866403667033692166353851)
  ·
    refine ⟨4299605500550538249530777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2866403667033692166353851 4299605500550538249530777)
    ·
      refine ⟨3224704125412903687148083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4299605500550538249530777 3224704125412903687148083)
      ·
        refine ⟨4837056188119355530722125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224704125412903687148083 4837056188119355530722125)
        ·
          refine ⟨1813896070544758324020797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4837056188119355530722125 1813896070544758324020797)
          ·
            refine ⟨680211026454284371507799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1813896070544758324020797 680211026454284371507799)
            ·
              refine ⟨1020316539681426557261699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680211026454284371507799 1020316539681426557261699)
              ·
                refine ⟨1530474809522139835892549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020316539681426557261699 1530474809522139835892549)
                ·
                  refine ⟨286964026785401219229853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530474809522139835892549 286964026785401219229853)
                  ·
                    rfl

theorem cell20_628718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_628718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628718 prefixEnd_628718 := by exact prefixLift 628718
  have htrace : WordTrace (prefixWord ++ tailWord_628718) baseStart_628718 baseEnd_628718 := by
    simpa [prefixWord, tailWord_628718, baseEnd_628718] using wordTrace_append hprefix tailTrace_628718
  have hstable : (prefixWord ++ tailWord_628718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628718).length < 2 ^ (prefixWord ++ tailWord_628718).sum := by decide
  have hdescent : baseEnd_628718 < baseStart_628718 := by decide
  rcases family_descends (prefixWord ++ tailWord_628718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628729 : List Nat := [1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_628729 : Nat := 118140960795 + 628729 * 2 ^ 59
def prefixEnd_628729 : Nat := 4983230072969 + 3 ^ 40 * 628729 * 2
def baseEnd_628729 : Nat := 95656349161711356621047

theorem tailTrace_628729 : CollatzResearch.WordTrace tailWord_628729 prefixEnd_628729 95656349161711356621047 := by
  unfold tailWord_628729
  simp only [CollatzResearch.WordTrace]
  refine ⟨22931630539229686209481241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15287753692819790806320827 22931630539229686209481241)
  ·
    refine ⟨17198722904422264657110931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22931630539229686209481241 17198722904422264657110931)
    ·
      refine ⟨25798084356633396985666397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17198722904422264657110931 25798084356633396985666397)
      ·
        refine ⟨9674281633737523869624899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25798084356633396985666397 9674281633737523869624899)
        ·
          refine ⟨14511422450606285804437349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9674281633737523869624899 14511422450606285804437349)
          ·
            refine ⟨2720891709488678588332003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14511422450606285804437349 2720891709488678588332003)
            ·
              refine ⟨4081337564233017882498005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720891709488678588332003 4081337564233017882498005)
              ·
                refine ⟨95656349161711356621047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4081337564233017882498005 95656349161711356621047)
                ·
                  rfl

theorem cell20_628729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_628729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628729 prefixEnd_628729 := by exact prefixLift 628729
  have htrace : WordTrace (prefixWord ++ tailWord_628729) baseStart_628729 baseEnd_628729 := by
    simpa [prefixWord, tailWord_628729, baseEnd_628729] using wordTrace_append hprefix tailTrace_628729
  have hstable : (prefixWord ++ tailWord_628729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628729).length < 2 ^ (prefixWord ++ tailWord_628729).sum := by decide
  have hdescent : baseEnd_628729 < baseStart_628729 := by decide
  rcases family_descends (prefixWord ++ tailWord_628729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628736 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_628736 : Nat := 118140960795 + 628736 * 2 ^ 59
def prefixEnd_628736 : Nat := 4983230072969 + 3 ^ 40 * 628736 * 2
def baseEnd_628736 : Nat := 286972242475873156629779

theorem tailTrace_628736 : CollatzResearch.WordTrace tailWord_628736 prefixEnd_628736 286972242475873156629779 := by
  unfold tailWord_628736
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465942925102163202493031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15287923900136217603324041 11465942925102163202493031)
  ·
    refine ⟨17198914387653244803739547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11465942925102163202493031 17198914387653244803739547)
    ·
      refine ⟨25798371581479867205609321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17198914387653244803739547 25798371581479867205609321)
      ·
        refine ⟨19348778686109900404206991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25798371581479867205609321 19348778686109900404206991)
        ·
          refine ⟨29023168029164850606310487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19348778686109900404206991 29023168029164850606310487)
          ·
            refine ⟨43534752043747275909465731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29023168029164850606310487 43534752043747275909465731)
            ·
              refine ⟨65302128065620913864198597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43534752043747275909465731 65302128065620913864198597)
              ·
                refine ⟨12244149012303921349537237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65302128065620913864198597 12244149012303921349537237)
                ·
                  refine ⟨286972242475873156629779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12244149012303921349537237 286972242475873156629779)
                  ·
                    rfl

theorem cell20_628736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_628736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628736 prefixEnd_628736 := by exact prefixLift 628736
  have htrace : WordTrace (prefixWord ++ tailWord_628736) baseStart_628736 baseEnd_628736 := by
    simpa [prefixWord, tailWord_628736, baseEnd_628736] using wordTrace_append hprefix tailTrace_628736
  have hstable : (prefixWord ++ tailWord_628736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628736).length < 2 ^ (prefixWord ++ tailWord_628736).sum := by decide
  have hdescent : baseEnd_628736 < baseStart_628736 := by decide
  rcases family_descends (prefixWord ++ tailWord_628736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628770 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_628770 : Nat := 118140960795 + 628770 * 2 ^ 59
def prefixEnd_628770 : Nat := 4983230072969 + 3 ^ 40 * 628770 * 2
def baseEnd_628770 : Nat := 286987761002320149496307

theorem tailTrace_628770 : CollatzResearch.WordTrace tailWord_628770 prefixEnd_628770 286987761002320149496307 := by
  unfold tailWord_628770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733281483020287552930941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15288750621387433474482509 5733281483020287552930941)
  ·
    refine ⟨2149980556132607832349103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5733281483020287552930941 2149980556132607832349103)
    ·
      refine ⟨3224970834198911748523655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149980556132607832349103 3224970834198911748523655)
      ·
        refine ⟨4837456251298367622785483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224970834198911748523655 4837456251298367622785483)
        ·
          refine ⟨7256184376947551434178225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837456251298367622785483 7256184376947551434178225)
          ·
            refine ⟨5442138282710663575633669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7256184376947551434178225 5442138282710663575633669)
            ·
              refine ⟨1020400928008249420431313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5442138282710663575633669 1020400928008249420431313)
              ·
                refine ⟨765300696006187065323485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020400928008249420431313 765300696006187065323485)
                ·
                  refine ⟨286987761002320149496307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765300696006187065323485 286987761002320149496307)
                  ·
                    rfl

theorem cell20_628770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_628770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628770 prefixEnd_628770 := by exact prefixLift 628770
  have htrace : WordTrace (prefixWord ++ tailWord_628770) baseStart_628770 baseEnd_628770 := by
    simpa [prefixWord, tailWord_628770, baseEnd_628770] using wordTrace_append hprefix tailTrace_628770
  have hstable : (prefixWord ++ tailWord_628770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628770).length < 2 ^ (prefixWord ++ tailWord_628770).sum := by decide
  have hdescent : baseEnd_628770 < baseStart_628770 := by decide
  rcases family_descends (prefixWord ++ tailWord_628770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628773 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 2]
def baseStart_628773 : Nat := 118140960795 + 628773 * 2 ^ 59
def prefixEnd_628773 : Nat := 4983230072969 + 3 ^ 40 * 628773 * 2
def baseEnd_628773 : Nat := 286989130284065472396295

theorem tailTrace_628773 : CollatzResearch.WordTrace tailWord_628773 prefixEnd_628773 286989130284065472396295 := by
  unfold tailWord_628773
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933235351070281724082973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15288823567380187816055315 22933235351070281724082973)
  ·
    refine ⟨8599963256651355646531115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22933235351070281724082973 8599963256651355646531115)
    ·
      refine ⟨12899944884977033469796673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8599963256651355646531115 12899944884977033469796673)
      ·
        refine ⟨9674958663732775102347505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12899944884977033469796673 9674958663732775102347505)
        ·
          refine ⟨7256218997799581326760629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9674958663732775102347505 7256218997799581326760629)
          ·
            refine ⟨680270531043710749383809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7256218997799581326760629 680270531043710749383809)
            ·
              refine ⟨510202898282783062037857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680270531043710749383809 510202898282783062037857)
              ·
                refine ⟨382652173712087296528393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510202898282783062037857 382652173712087296528393)
                ·
                  refine ⟨286989130284065472396295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382652173712087296528393 286989130284065472396295)
                  ·
                    rfl

theorem cell20_628773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_628773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628773 prefixEnd_628773 := by exact prefixLift 628773
  have htrace : WordTrace (prefixWord ++ tailWord_628773) baseStart_628773 baseEnd_628773 := by
    simpa [prefixWord, tailWord_628773, baseEnd_628773] using wordTrace_append hprefix tailTrace_628773
  have hstable : (prefixWord ++ tailWord_628773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628773).length < 2 ^ (prefixWord ++ tailWord_628773).sum := by decide
  have hdescent : baseEnd_628773 < baseStart_628773 := by decide
  rcases family_descends (prefixWord ++ tailWord_628773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628784 : List Nat := [2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_628784 : Nat := 118140960795 + 628784 * 2 ^ 59
def prefixEnd_628784 : Nat := 4983230072969 + 3 ^ 40 * 628784 * 2
def baseEnd_628784 : Nat := 95664716994599441009861

theorem tailTrace_628784 : CollatzResearch.WordTrace tailWord_628784 prefixEnd_628784 95664716994599441009861 := by
  unfold tailWord_628784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466818277015215301366703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15289091036020287068488937 11466818277015215301366703)
  ·
    refine ⟨17200227415522822952050055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11466818277015215301366703 17200227415522822952050055)
    ·
      refine ⟨25800341123284234428075083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17200227415522822952050055 25800341123284234428075083)
      ·
        refine ⟨38700511684926351642112625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25800341123284234428075083 38700511684926351642112625)
        ·
          refine ⟨29025383763694763731584469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38700511684926351642112625 29025383763694763731584469)
          ·
            refine ⟨680282431961596024959011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29025383763694763731584469 680282431961596024959011)
            ·
              refine ⟨1020423647942394037438517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680282431961596024959011 1020423647942394037438517)
              ·
                refine ⟨95664716994599441009861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1020423647942394037438517 95664716994599441009861)
                ·
                  rfl

theorem cell20_628784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_628784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628784 prefixEnd_628784 := by exact prefixLift 628784
  have htrace : WordTrace (prefixWord ++ tailWord_628784) baseStart_628784 baseEnd_628784 := by
    simpa [prefixWord, tailWord_628784, baseEnd_628784] using wordTrace_append hprefix tailTrace_628784
  have hstable : (prefixWord ++ tailWord_628784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628784).length < 2 ^ (prefixWord ++ tailWord_628784).sum := by decide
  have hdescent : baseEnd_628784 < baseStart_628784 := by decide
  rcases family_descends (prefixWord ++ tailWord_628784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628791 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_628791 : Nat := 118140960795 + 628791 * 2 ^ 59
def prefixEnd_628791 : Nat := 4983230072969 + 3 ^ 40 * 628791 * 2
def baseEnd_628791 : Nat := 286997345974537409796221

theorem tailTrace_628791 : CollatzResearch.WordTrace tailWord_628791 prefixEnd_628791 286997345974537409796221 := by
  unfold tailWord_628791
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933891865005070798238227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15289261243336713865492151 22933891865005070798238227)
  ·
    refine ⟨34400837797507606197357341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22933891865005070798238227 34400837797507606197357341)
    ·
      refine ⟨12900314174065352324009003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34400837797507606197357341 12900314174065352324009003)
      ·
        refine ⟨19350471261098028486013505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12900314174065352324009003 19350471261098028486013505)
        ·
          refine ⟨14512853445823521364510129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19350471261098028486013505 14512853445823521364510129)
          ·
            refine ⟨10884640084367641023382597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14512853445823521364510129 10884640084367641023382597)
            ·
              refine ⟨2040870015818932691884237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10884640084367641023382597 2040870015818932691884237)
              ·
                refine ⟨765326255932099759456589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2040870015818932691884237 765326255932099759456589)
                ·
                  refine ⟨286997345974537409796221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765326255932099759456589 286997345974537409796221)
                  ·
                    rfl

theorem cell20_628791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_628791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628791 prefixEnd_628791 := by exact prefixLift 628791
  have htrace : WordTrace (prefixWord ++ tailWord_628791) baseStart_628791 baseEnd_628791 := by
    simpa [prefixWord, tailWord_628791, baseEnd_628791] using wordTrace_append hprefix tailTrace_628791
  have hstable : (prefixWord ++ tailWord_628791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628791).length < 2 ^ (prefixWord ++ tailWord_628791).sum := by decide
  have hdescent : baseEnd_628791 < baseStart_628791 := by decide
  rcases family_descends (prefixWord ++ tailWord_628791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628801 : List Nat := [1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_628801 : Nat := 118140960795 + 628801 * 2 ^ 59
def prefixEnd_628801 : Nat := 4983230072969 + 3 ^ 40 * 628801 * 2
def baseEnd_628801 : Nat := 95667303415673939820949

theorem tailTrace_628801 : CollatzResearch.WordTrace tailWord_628801 prefixEnd_628801 95667303415673939820949 := by
  unfold tailWord_628801
  simp only [CollatzResearch.WordTrace]
  refine ⟨22934256594968842506102257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15289504396645895004068171 22934256594968842506102257)
  ·
    refine ⟨17200692446226631879576693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22934256594968842506102257 17200692446226631879576693)
    ·
      refine ⟨1612564916833746738710315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17200692446226631879576693 1612564916833746738710315)
      ·
        refine ⟨2418847375250620108065473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612564916833746738710315 2418847375250620108065473)
        ·
          refine ⟨1814135531437965081049105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418847375250620108065473 1814135531437965081049105)
          ·
            refine ⟨1360601648578473810786829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814135531437965081049105 1360601648578473810786829)
            ·
              refine ⟨510225618216927679045061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1360601648578473810786829 510225618216927679045061)
              ·
                refine ⟨95667303415673939820949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510225618216927679045061 95667303415673939820949)
                ·
                  rfl

theorem cell20_628801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_628801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628801 prefixEnd_628801 := by exact prefixLift 628801
  have htrace : WordTrace (prefixWord ++ tailWord_628801) baseStart_628801 baseEnd_628801 := by
    simpa [prefixWord, tailWord_628801, baseEnd_628801] using wordTrace_append hprefix tailTrace_628801
  have hstable : (prefixWord ++ tailWord_628801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628801).length < 2 ^ (prefixWord ++ tailWord_628801).sum := by decide
  have hdescent : baseEnd_628801 < baseStart_628801 := by decide
  rcases family_descends (prefixWord ++ tailWord_628801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628836 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_628836 : Nat := 118140960795 + 628836 * 2 ^ 59
def prefixEnd_628836 : Nat := 4983230072969 + 3 ^ 40 * 628836 * 2
def baseEnd_628836 : Nat := 287017885200717253296037

theorem tailTrace_628836 : CollatzResearch.WordTrace tailWord_628836 prefixEnd_628836 287017885200717253296037 := by
  unfold tailWord_628836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467766574921021741813181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15290355433228028989084241 11467766574921021741813181)
  ·
    refine ⟨4300412465595383153179943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11467766574921021741813181 4300412465595383153179943)
    ·
      refine ⟨6450618698393074729769915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4300412465595383153179943 6450618698393074729769915)
      ·
        refine ⟨9675928047589612094654873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450618698393074729769915 9675928047589612094654873)
        ·
          refine ⟨7256946035692209070991155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9675928047589612094654873 7256946035692209070991155)
          ·
            refine ⟨10885419053538313606486733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7256946035692209070991155 10885419053538313606486733)
            ·
              refine ⟨4082032145076867602432525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10885419053538313606486733 4082032145076867602432525)
              ·
                refine ⟨1530762054403825350912197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4082032145076867602432525 1530762054403825350912197)
                ·
                  refine ⟨287017885200717253296037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530762054403825350912197 287017885200717253296037)
                  ·
                    rfl

theorem cell20_628836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_628836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628836 prefixEnd_628836 := by exact prefixLift 628836
  have htrace : WordTrace (prefixWord ++ tailWord_628836) baseStart_628836 baseEnd_628836 := by
    simpa [prefixWord, tailWord_628836, baseEnd_628836] using wordTrace_append hprefix tailTrace_628836
  have hstable : (prefixWord ++ tailWord_628836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628836).length < 2 ^ (prefixWord ++ tailWord_628836).sum := by decide
  have hdescent : baseEnd_628836 < baseStart_628836 := by decide
  rcases family_descends (prefixWord ++ tailWord_628836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628860 : List Nat := [2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_628860 : Nat := 118140960795 + 628860 * 2 ^ 59
def prefixEnd_628860 : Nat := 4983230072969 + 3 ^ 40 * 628860 * 2
def baseEnd_628860 : Nat := 95676279818226612165313

theorem tailTrace_628860 : CollatzResearch.WordTrace tailWord_628860 prefixEnd_628860 95676279818226612165313 := by
  unfold tailWord_628860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468204250877547791250017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15290939001170063721666689 11468204250877547791250017)
  ·
    refine ⟨8601153188158160843437513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11468204250877547791250017 8601153188158160843437513)
    ·
      refine ⟨6450864891118620632578135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8601153188158160843437513 6450864891118620632578135)
      ·
        refine ⟨9676297336677930948867203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450864891118620632578135 9676297336677930948867203)
        ·
          refine ⟨14514446005016896423300805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676297336677930948867203 14514446005016896423300805)
          ·
            refine ⟨2721458625940668079368901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14514446005016896423300805 2721458625940668079368901)
            ·
              refine ⟨510273492363875264881669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2721458625940668079368901 510273492363875264881669)
              ·
                refine ⟨95676279818226612165313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510273492363875264881669 95676279818226612165313)
                ·
                  rfl

theorem cell20_628860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_628860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628860 prefixEnd_628860 := by exact prefixLift 628860
  have htrace : WordTrace (prefixWord ++ tailWord_628860) baseStart_628860 baseEnd_628860 := by
    simpa [prefixWord, tailWord_628860, baseEnd_628860] using wordTrace_append hprefix tailTrace_628860
  have hstable : (prefixWord ++ tailWord_628860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628860).length < 2 ^ (prefixWord ++ tailWord_628860).sum := by decide
  have hdescent : baseEnd_628860 < baseStart_628860 := by decide
  rcases family_descends (prefixWord ++ tailWord_628860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628887 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 2]
def baseStart_628887 : Nat := 118140960795 + 628887 * 2 ^ 59
def prefixEnd_628887 : Nat := 4983230072969 + 3 ^ 40 * 628887 * 2
def baseEnd_628887 : Nat := 287041162990387742595829

theorem tailTrace_628887 : CollatzResearch.WordTrace tailWord_628887 prefixEnd_628887 287041162990387742595829 := by
  unfold tailWord_628887
  simp only [CollatzResearch.WordTrace]
  refine ⟨22937393272657279193732915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15291595515104852795821943 22937393272657279193732915)
  ·
    refine ⟨34406089908985918790599373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22937393272657279193732915 34406089908985918790599373)
    ·
      refine ⟨12902283715869719546474765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34406089908985918790599373 12902283715869719546474765)
      ·
        refine ⟨4838356393451144829928037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12902283715869719546474765 4838356393451144829928037)
        ·
          refine ⟨907191823772089655611507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4838356393451144829928037 907191823772089655611507)
          ·
            refine ⟨1360787735658134483417261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907191823772089655611507 1360787735658134483417261)
            ·
              refine ⟨510295400871800431281473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1360787735658134483417261 510295400871800431281473)
              ·
                refine ⟨382721550653850323461105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510295400871800431281473 382721550653850323461105)
                ·
                  refine ⟨287041162990387742595829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382721550653850323461105 287041162990387742595829)
                  ·
                    rfl

theorem cell20_628887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2].length) (baseStart_628887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628887 prefixEnd_628887 := by exact prefixLift 628887
  have htrace : WordTrace (prefixWord ++ tailWord_628887) baseStart_628887 baseEnd_628887 := by
    simpa [prefixWord, tailWord_628887, baseEnd_628887] using wordTrace_append hprefix tailTrace_628887
  have hstable : (prefixWord ++ tailWord_628887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628887).length < 2 ^ (prefixWord ++ tailWord_628887).sum := by decide
  have hdescent : baseEnd_628887 < baseStart_628887 := by decide
  rcases family_descends (prefixWord ++ tailWord_628887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628898 : List Nat := [3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_628898 : Nat := 118140960795 + 628898 * 2 ^ 59
def prefixEnd_628898 : Nat := 4983230072969 + 3 ^ 40 * 628898 * 2
def baseEnd_628898 : Nat := 95682061230040197743039

theorem tailTrace_628898 : CollatzResearch.WordTrace tailWord_628898 prefixEnd_628898 95682061230040197743039 := by
  unfold tailWord_628898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734448618904357018095837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15291862983744952048255565 5734448618904357018095837)
  ·
    refine ⟨2150418232089133881785939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5734448618904357018095837 2150418232089133881785939)
    ·
      refine ⟨3225627348133700822678909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150418232089133881785939 3225627348133700822678909)
      ·
        refine ⟨1209610255550137808504591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3225627348133700822678909 1209610255550137808504591)
        ·
          refine ⟨1814415383325206712756887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209610255550137808504591 1814415383325206712756887)
          ·
            refine ⟨2721623074987810069135331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814415383325206712756887 2721623074987810069135331)
            ·
              refine ⟨4082434612481715103702997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721623074987810069135331 4082434612481715103702997)
              ·
                refine ⟨95682061230040197743039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4082434612481715103702997 95682061230040197743039)
                ·
                  rfl

theorem cell20_628898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_628898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628898 prefixEnd_628898 := by exact prefixLift 628898
  have htrace : WordTrace (prefixWord ++ tailWord_628898) baseStart_628898 baseEnd_628898 := by
    simpa [prefixWord, tailWord_628898, baseEnd_628898] using wordTrace_append hprefix tailTrace_628898
  have hstable : (prefixWord ++ tailWord_628898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628898).length < 2 ^ (prefixWord ++ tailWord_628898).sum := by decide
  have hdescent : baseEnd_628898 < baseStart_628898 := by decide
  rcases family_descends (prefixWord ++ tailWord_628898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628919 : List Nat := [1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_628919 : Nat := 118140960795 + 628919 * 2 ^ 59
def prefixEnd_628919 : Nat := 4983230072969 + 3 ^ 40 * 628919 * 2
def baseEnd_628919 : Nat := 95685256220779284509677

theorem tailTrace_628919 : CollatzResearch.WordTrace tailWord_628919 prefixEnd_628919 95685256220779284509677 := by
  unfold tailWord_628919
  simp only [CollatzResearch.WordTrace]
  refine ⟨22938560408541348658897811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15292373605694232439265207 22938560408541348658897811)
  ·
    refine ⟨34407840612812022988346717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22938560408541348658897811 34407840612812022988346717)
    ·
      refine ⟨12902940229804508620630019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34407840612812022988346717 12902940229804508620630019)
      ·
        refine ⟨19354410344706762930945029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12902940229804508620630019 19354410344706762930945029)
        ·
          refine ⟨3628951939632518049552193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19354410344706762930945029 3628951939632518049552193)
          ·
            refine ⟨2721713954724388537164145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3628951939632518049552193 2721713954724388537164145)
            ·
              refine ⟨2041285466043291402873109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721713954724388537164145 2041285466043291402873109)
              ·
                refine ⟨95685256220779284509677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2041285466043291402873109 95685256220779284509677)
                ·
                  rfl

theorem cell20_628919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_628919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628919 prefixEnd_628919 := by exact prefixLift 628919
  have htrace : WordTrace (prefixWord ++ tailWord_628919) baseStart_628919 baseEnd_628919 := by
    simpa [prefixWord, tailWord_628919, baseEnd_628919] using wordTrace_append hprefix tailTrace_628919
  have hstable : (prefixWord ++ tailWord_628919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628919).length < 2 ^ (prefixWord ++ tailWord_628919).sum := by decide
  have hdescent : baseEnd_628919 < baseStart_628919 := by decide
  rcases family_descends (prefixWord ++ tailWord_628919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628943 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_628943 : Nat := 118140960795 + 628943 * 2 ^ 59
def prefixEnd_628943 : Nat := 4983230072969 + 3 ^ 40 * 628943 * 2
def baseEnd_628943 : Nat := 287066722916300436728933

theorem tailTrace_628943 : CollatzResearch.WordTrace tailWord_628943 prefixEnd_628943 287066722916300436728933 := by
  unfold tailWord_628943
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939435760454400757771483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15292957173636267171847655 22939435760454400757771483)
  ·
    refine ⟨34409153640681601136657225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22939435760454400757771483 34409153640681601136657225)
    ·
      refine ⟨25806865230511200852492919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34409153640681601136657225 25806865230511200852492919)
      ·
        refine ⟨38710297845766801278739379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25806865230511200852492919 38710297845766801278739379)
        ·
          refine ⟨58065446768650201918109069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38710297845766801278739379 58065446768650201918109069)
          ·
            refine ⟨21774542538243825719290901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58065446768650201918109069 21774542538243825719290901)
            ·
              refine ⟨1020681681480179330591761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21774542538243825719290901 1020681681480179330591761)
              ·
                refine ⟨765511261110134497943821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020681681480179330591761 765511261110134497943821)
                ·
                  refine ⟨287066722916300436728933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765511261110134497943821 287066722916300436728933)
                  ·
                    rfl

theorem cell20_628943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_628943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628943 prefixEnd_628943 := by exact prefixLift 628943
  have htrace : WordTrace (prefixWord ++ tailWord_628943) baseStart_628943 baseEnd_628943 := by
    simpa [prefixWord, tailWord_628943, baseEnd_628943] using wordTrace_append hprefix tailTrace_628943
  have hstable : (prefixWord ++ tailWord_628943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628943).length < 2 ^ (prefixWord ++ tailWord_628943).sum := by decide
  have hdescent : baseEnd_628943 < baseStart_628943 := by decide
  rcases family_descends (prefixWord ++ tailWord_628943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628946 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_628946 : Nat := 118140960795 + 628946 * 2 ^ 59
def prefixEnd_628946 : Nat := 4983230072969 + 3 ^ 40 * 628946 * 2
def baseEnd_628946 : Nat := 287068092198045759628921

theorem tailTrace_628946 : CollatzResearch.WordTrace tailWord_628946 prefixEnd_628946 287068092198045759628921 := by
  unfold tailWord_628946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734886294860883067532673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15293030119629021513420461 5734886294860883067532673)
  ·
    refine ⟨4301164721145662300649505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5734886294860883067532673 4301164721145662300649505)
    ·
      refine ⟨3225873540859246725487129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4301164721145662300649505 3225873540859246725487129)
      ·
        refine ⟨2419405155644435044115347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3225873540859246725487129 2419405155644435044115347)
        ·
          refine ⟨3629107733466652566173021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419405155644435044115347 3629107733466652566173021)
          ·
            refine ⟨1360915400049994712314883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3629107733466652566173021 1360915400049994712314883)
            ·
              refine ⟨2041373100074992068472325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360915400049994712314883 2041373100074992068472325)
              ·
                refine ⟨382757456264061012838561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2041373100074992068472325 382757456264061012838561)
                ·
                  refine ⟨287068092198045759628921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382757456264061012838561 287068092198045759628921)
                  ·
                    rfl

theorem cell20_628946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_628946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628946 prefixEnd_628946 := by exact prefixLift 628946
  have htrace : WordTrace (prefixWord ++ tailWord_628946) baseStart_628946 baseEnd_628946 := by
    simpa [prefixWord, tailWord_628946, baseEnd_628946] using wordTrace_append hprefix tailTrace_628946
  have hstable : (prefixWord ++ tailWord_628946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628946).length < 2 ^ (prefixWord ++ tailWord_628946).sum := by decide
  have hdescent : baseEnd_628946 < baseStart_628946 := by decide
  rcases family_descends (prefixWord ++ tailWord_628946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628964 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_628964 : Nat := 118140960795 + 628964 * 2 ^ 59
def prefixEnd_628964 : Nat := 4983230072969 + 3 ^ 40 * 628964 * 2
def baseEnd_628964 : Nat := 287076307888517697028847

theorem tailTrace_628964 : CollatzResearch.WordTrace tailWord_628964 prefixEnd_628964 287076307888517697028847 := by
  unfold tailWord_628964
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470100846689160672142973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15293467795585547562857297 11470100846689160672142973)
  ·
    refine ⟨4301287817508435252053615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11470100846689160672142973 4301287817508435252053615)
    ·
      refine ⟨6451931726262652878080423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301287817508435252053615 6451931726262652878080423)
      ·
        refine ⟨9677897589393979317120635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451931726262652878080423 9677897589393979317120635)
        ·
          refine ⟨14516846384090968975680953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677897589393979317120635 14516846384090968975680953)
          ·
            refine ⟨10887634788068226731760715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14516846384090968975680953 10887634788068226731760715)
            ·
              refine ⟨16331452182102340097641073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10887634788068226731760715 16331452182102340097641073)
              ·
                refine ⟨12248589136576755073230805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16331452182102340097641073 12248589136576755073230805)
                ·
                  refine ⟨287076307888517697028847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12248589136576755073230805 287076307888517697028847)
                  ·
                    rfl

theorem cell20_628964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_628964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628964 prefixEnd_628964 := by exact prefixLift 628964
  have htrace : WordTrace (prefixWord ++ tailWord_628964) baseStart_628964 baseEnd_628964 := by
    simpa [prefixWord, tailWord_628964, baseEnd_628964] using wordTrace_append hprefix tailTrace_628964
  have hstable : (prefixWord ++ tailWord_628964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628964).length < 2 ^ (prefixWord ++ tailWord_628964).sum := by decide
  have hdescent : baseEnd_628964 < baseStart_628964 := by decide
  rcases family_descends (prefixWord ++ tailWord_628964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628967 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_628967 : Nat := 118140960795 + 628967 * 2 ^ 59
def prefixEnd_628967 : Nat := 4983230072969 + 3 ^ 40 * 628967 * 2
def baseEnd_628967 : Nat := 287077677170263019928835

theorem tailTrace_628967 : CollatzResearch.WordTrace tailWord_628967 prefixEnd_628967 287077677170263019928835 := by
  unfold tailWord_628967
  simp only [CollatzResearch.WordTrace]
  refine ⟨22940311112367452856645155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15293540741578301904430103 22940311112367452856645155)
  ·
    refine ⟨34410466668551179284967733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22940311112367452856645155 34410466668551179284967733)
    ·
      refine ⟨3225981250176673057965725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34410466668551179284967733 3225981250176673057965725)
      ·
        refine ⟨1209742968816252396737147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3225981250176673057965725 1209742968816252396737147)
        ·
          refine ⟨1814614453224378595105721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209742968816252396737147 1814614453224378595105721)
          ·
            refine ⟨1360960839918283946329291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814614453224378595105721 1360960839918283946329291)
            ·
              refine ⟨2041441259877425919493937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360960839918283946329291 2041441259877425919493937)
              ·
                refine ⟨1531080944908069439620453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041441259877425919493937 1531080944908069439620453)
                ·
                  refine ⟨287077677170263019928835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531080944908069439620453 287077677170263019928835)
                  ·
                    rfl

theorem cell20_628967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_628967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_628967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_628967 prefixEnd_628967 := by exact prefixLift 628967
  have htrace : WordTrace (prefixWord ++ tailWord_628967) baseStart_628967 baseEnd_628967 := by
    simpa [prefixWord, tailWord_628967, baseEnd_628967] using wordTrace_append hprefix tailTrace_628967
  have hstable : (prefixWord ++ tailWord_628967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628967).length < 2 ^ (prefixWord ++ tailWord_628967).sum := by decide
  have hdescent : baseEnd_628967 < baseStart_628967 := by decide
  rcases family_descends (prefixWord ++ tailWord_628967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629022 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_629022 : Nat := 118140960795 + 629022 * 2 ^ 59
def prefixEnd_629022 : Nat := 4983230072969 + 3 ^ 40 * 629022 * 2
def baseEnd_629022 : Nat := 287102780668927273095277

theorem tailTrace_629022 : CollatzResearch.WordTrace tailWord_629022 prefixEnd_629022 287102780668927273095277 := by
  unfold tailWord_629022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867789640896024656237165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15294878084778798166598213 2867789640896024656237165)
  ·
    refine ⟨1075421115336009246088937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2867789640896024656237165 1075421115336009246088937)
    ·
      refine ⟨806565836502006934566703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075421115336009246088937 806565836502006934566703)
      ·
        refine ⟨1209848754753010401850055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806565836502006934566703 1209848754753010401850055)
        ·
          refine ⟨1814773132129515602775083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209848754753010401850055 1814773132129515602775083)
          ·
            refine ⟨2722159698194273404162625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814773132129515602775083 2722159698194273404162625)
            ·
              refine ⟨2041619773645705053121969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722159698194273404162625 2041619773645705053121969)
              ·
                refine ⟨1531214830234278789841477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041619773645705053121969 1531214830234278789841477)
                ·
                  refine ⟨287102780668927273095277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531214830234278789841477 287102780668927273095277)
                  ·
                    rfl

theorem cell20_629022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_629022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629022 prefixEnd_629022 := by exact prefixLift 629022
  have htrace : WordTrace (prefixWord ++ tailWord_629022) baseStart_629022 baseEnd_629022 := by
    simpa [prefixWord, tailWord_629022, baseEnd_629022] using wordTrace_append hprefix tailTrace_629022
  have hstable : (prefixWord ++ tailWord_629022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629022).length < 2 ^ (prefixWord ++ tailWord_629022).sum := by decide
  have hdescent : baseEnd_629022 < baseStart_629022 := by decide
  rcases family_descends (prefixWord ++ tailWord_629022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629029 : List Nat := [1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_629029 : Nat := 118140960795 + 629029 * 2 ^ 59
def prefixEnd_629029 : Nat := 4983230072969 + 3 ^ 40 * 629029 * 2
def baseEnd_629029 : Nat := 95701991886555453287305

theorem tailTrace_629029 : CollatzResearch.WordTrace tailWord_629029 prefixEnd_629029 95701991886555453287305 := by
  unfold tailWord_629029
  simp only [CollatzResearch.WordTrace]
  refine ⟨22942572438142837445402141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15295048292095224963601427 22942572438142837445402141)
  ·
    refine ⟨8603464664303564042025803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22942572438142837445402141 8603464664303564042025803)
    ·
      refine ⟨12905196996455346063038705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8603464664303564042025803 12905196996455346063038705)
      ·
        refine ⟨9678897747341509547279029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12905196996455346063038705 9678897747341509547279029)
        ·
          refine ⟨907396663813266520057409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9678897747341509547279029 907396663813266520057409)
          ·
            refine ⟨680547497859949890043057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907396663813266520057409 680547497859949890043057)
            ·
              refine ⟨510410623394962417532293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680547497859949890043057 510410623394962417532293)
              ·
                refine ⟨95701991886555453287305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510410623394962417532293 95701991886555453287305)
                ·
                  rfl

theorem cell20_629029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_629029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629029 prefixEnd_629029 := by exact prefixLift 629029
  have htrace : WordTrace (prefixWord ++ tailWord_629029) baseStart_629029 baseEnd_629029 := by
    simpa [prefixWord, tailWord_629029, baseEnd_629029] using wordTrace_append hprefix tailTrace_629029
  have hstable : (prefixWord ++ tailWord_629029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629029).length < 2 ^ (prefixWord ++ tailWord_629029).sum := by decide
  have hdescent : baseEnd_629029 < baseStart_629029 := by decide
  rcases family_descends (prefixWord ++ tailWord_629029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629047 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_629047 : Nat := 118140960795 + 629047 * 2 ^ 59
def prefixEnd_629047 : Nat := 4983230072969 + 3 ^ 40 * 629047 * 2
def baseEnd_629047 : Nat := 287114191350138297261841

theorem tailTrace_629047 : CollatzResearch.WordTrace tailWord_629047 prefixEnd_629047 287114191350138297261841 := by
  unfold tailWord_629047
  simp only [CollatzResearch.WordTrace]
  refine ⟨22943228952077626519557395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15295485968051751013038263 22943228952077626519557395)
  ·
    refine ⟨34414843428116439779336093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22943228952077626519557395 34414843428116439779336093)
    ·
      refine ⟨12905566285543664917251035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34414843428116439779336093 12905566285543664917251035)
      ·
        refine ⟨19358349428315497375876553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12905566285543664917251035 19358349428315497375876553)
        ·
          refine ⟨14518762071236623031907415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19358349428315497375876553 14518762071236623031907415)
          ·
            refine ⟨21778143106854934547861123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14518762071236623031907415 21778143106854934547861123)
            ·
              refine ⟨32667214660282401821791685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21778143106854934547861123 32667214660282401821791685)
              ·
                refine ⟨6125102748802950341585941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32667214660282401821791685 6125102748802950341585941)
                ·
                  refine ⟨287114191350138297261841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6125102748802950341585941 287114191350138297261841)
                  ·
                    rfl

theorem cell20_629047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_629047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629047 prefixEnd_629047 := by exact prefixLift 629047
  have htrace : WordTrace (prefixWord ++ tailWord_629047) baseStart_629047 baseEnd_629047 := by
    simpa [prefixWord, tailWord_629047, baseEnd_629047] using wordTrace_append hprefix tailTrace_629047
  have hstable : (prefixWord ++ tailWord_629047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629047).length < 2 ^ (prefixWord ++ tailWord_629047).sum := by decide
  have hdescent : baseEnd_629047 < baseStart_629047 := by decide
  rcases family_descends (prefixWord ++ tailWord_629047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629064 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_629064 : Nat := 118140960795 + 629064 * 2 ^ 59
def prefixEnd_629064 : Nat := 4983230072969 + 3 ^ 40 * 629064 * 2
def baseEnd_629064 : Nat := 287121950613361793695105

theorem tailTrace_629064 : CollatzResearch.WordTrace tailWord_629064 prefixEnd_629064 287121950613361793695105 := by
  unfold tailWord_629064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471924496508019211463123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15295899328677358948617497 11471924496508019211463123)
  ·
    refine ⟨17207886744762028817194685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11471924496508019211463123 17207886744762028817194685)
    ·
      refine ⟨6452957529285760806448007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17207886744762028817194685 6452957529285760806448007)
      ·
        refine ⟨9679436293928641209672011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6452957529285760806448007 9679436293928641209672011)
        ·
          refine ⟨14519154440892961814508017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679436293928641209672011 14519154440892961814508017)
          ·
            refine ⟨10889365830669721360881013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14519154440892961814508017 10889365830669721360881013)
            ·
              refine ⟨1020878046625286377582595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10889365830669721360881013 1020878046625286377582595)
              ·
                refine ⟨1531317069937929566373893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020878046625286377582595 1531317069937929566373893)
                ·
                  refine ⟨287121950613361793695105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1531317069937929566373893 287121950613361793695105)
                  ·
                    rfl

theorem cell20_629064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_629064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629064 prefixEnd_629064 := by exact prefixLift 629064
  have htrace : WordTrace (prefixWord ++ tailWord_629064) baseStart_629064 baseEnd_629064 := by
    simpa [prefixWord, tailWord_629064, baseEnd_629064] using wordTrace_append hprefix tailTrace_629064
  have hstable : (prefixWord ++ tailWord_629064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629064).length < 2 ^ (prefixWord ++ tailWord_629064).sum := by decide
  have hdescent : baseEnd_629064 < baseStart_629064 := by decide
  rcases family_descends (prefixWord ++ tailWord_629064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629074 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_629074 : Nat := 118140960795 + 629074 * 2 ^ 59
def prefixEnd_629074 : Nat := 4983230072969 + 3 ^ 40 * 629074 * 2
def baseEnd_629074 : Nat := 287126514885846203361731

theorem tailTrace_629074 : CollatzResearch.WordTrace tailWord_629074 prefixEnd_629074 287126514885846203361731 := by
  unfold tailWord_629074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736053430744952532697569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15296142481986540087193517 5736053430744952532697569)
  ·
    refine ⟨4302040073058714399523177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5736053430744952532697569 4302040073058714399523177)
    ·
      refine ⟨3226530054794035799642383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4302040073058714399523177 3226530054794035799642383)
      ·
        refine ⟨4839795082191053699463575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226530054794035799642383 4839795082191053699463575)
        ·
          refine ⟨7259692623286580549195363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4839795082191053699463575 7259692623286580549195363)
          ·
            refine ⟨10889538934929870823793045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259692623286580549195363 10889538934929870823793045)
            ·
              refine ⟨510447137574837694865299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10889538934929870823793045 510447137574837694865299)
              ·
                refine ⟨765670706362256542297949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510447137574837694865299 765670706362256542297949)
                ·
                  refine ⟨287126514885846203361731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765670706362256542297949 287126514885846203361731)
                  ·
                    rfl

theorem cell20_629074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_629074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629074 prefixEnd_629074 := by exact prefixLift 629074
  have htrace : WordTrace (prefixWord ++ tailWord_629074) baseStart_629074 baseEnd_629074 := by
    simpa [prefixWord, tailWord_629074, baseEnd_629074] using wordTrace_append hprefix tailTrace_629074
  have hstable : (prefixWord ++ tailWord_629074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629074).length < 2 ^ (prefixWord ++ tailWord_629074).sum := by decide
  have hdescent : baseEnd_629074 < baseStart_629074 := by decide
  rcases family_descends (prefixWord ++ tailWord_629074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629109 : List Nat := [1, 3, 4, 1, 2, 9]
def baseStart_629109 : Nat := 118140960795 + 629109 * 2 ^ 59
def prefixEnd_629109 : Nat := 4983230072969 + 3 ^ 40 * 629109 * 2
def baseEnd_629109 : Nat := 10634907031094134710923

theorem tailTrace_629109 : CollatzResearch.WordTrace tailWord_629109 prefixEnd_629109 10634907031094134710923 := by
  unfold tailWord_629109
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945490277853011108314381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15296993518568674072209587 22945490277853011108314381)
  ·
    refine ⟨8604558854194879165617893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22945490277853011108314381 8604558854194879165617893)
    ·
      refine ⟨1613354785161539843553355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8604558854194879165617893 1613354785161539843553355)
      ·
        refine ⟨2420032177742309765330033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613354785161539843553355 2420032177742309765330033)
        ·
          refine ⟨1815024133306732323997525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2420032177742309765330033 1815024133306732323997525)
          ·
            refine ⟨10634907031094134710923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1815024133306732323997525 10634907031094134710923)
            ·
              rfl

theorem cell20_629109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 9].length) (baseStart_629109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629109 prefixEnd_629109 := by exact prefixLift 629109
  have htrace : WordTrace (prefixWord ++ tailWord_629109) baseStart_629109 baseEnd_629109 := by
    simpa [prefixWord, tailWord_629109, baseEnd_629109] using wordTrace_append hprefix tailTrace_629109
  have hstable : (prefixWord ++ tailWord_629109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629109).length < 2 ^ (prefixWord ++ tailWord_629109).sum := by decide
  have hdescent : baseEnd_629109 < baseStart_629109 := by decide
  rcases family_descends (prefixWord ++ tailWord_629109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629122 : List Nat := [3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_629122 : Nat := 118140960795 + 629122 * 2 ^ 59
def prefixEnd_629122 : Nat := 4983230072969 + 3 ^ 40 * 629122 * 2
def baseEnd_629122 : Nat := 95716141131257123253845

theorem tailTrace_629122 : CollatzResearch.WordTrace tailWord_629122 prefixEnd_629122 95716141131257123253845 := by
  unfold tailWord_629122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736491106701478582134405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15297309617870609552358413 5736491106701478582134405)
  ·
    refine ⟨1075592082506527234150201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5736491106701478582134405 1075592082506527234150201)
    ·
      refine ⟨806694061879895425612651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075592082506527234150201 806694061879895425612651)
      ·
        refine ⟨1210041092819843138418977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806694061879895425612651 1210041092819843138418977)
        ·
          refine ⟨907530819614882353814233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210041092819843138418977 907530819614882353814233)
          ·
            refine ⟨680648114711161765360675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907530819614882353814233 680648114711161765360675)
            ·
              refine ⟨1020972172066742648041013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680648114711161765360675 1020972172066742648041013)
              ·
                refine ⟨95716141131257123253845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1020972172066742648041013 95716141131257123253845)
                ·
                  rfl

theorem cell20_629122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_629122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629122 prefixEnd_629122 := by exact prefixLift 629122
  have htrace : WordTrace (prefixWord ++ tailWord_629122) baseStart_629122 baseEnd_629122 := by
    simpa [prefixWord, tailWord_629122, baseEnd_629122] using wordTrace_append hprefix tailTrace_629122
  have hstable : (prefixWord ++ tailWord_629122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629122).length < 2 ^ (prefixWord ++ tailWord_629122).sum := by decide
  have hdescent : baseEnd_629122 < baseStart_629122 := by decide
  rcases family_descends (prefixWord ++ tailWord_629122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629153 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 2]
def baseStart_629153 : Nat := 118140960795 + 629153 * 2 ^ 59
def prefixEnd_629153 : Nat := 4983230072969 + 3 ^ 40 * 629153 * 2
def baseEnd_629153 : Nat := 287162572638473039728075

theorem tailTrace_629153 : CollatzResearch.WordTrace tailWord_629153 prefixEnd_629153 287162572638473039728075 := by
  unfold tailWord_629153
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947095089693606622916113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15298063393129071081944075 22947095089693606622916113)
  ·
    refine ⟨17210321317270204967187085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22947095089693606622916113 17210321317270204967187085)
    ·
      refine ⟨6453870493976326862695157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17210321317270204967187085 6453870493976326862695157)
      ·
        refine ⟨605050358810280643377671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6453870493976326862695157 605050358810280643377671)
        ·
          refine ⟨907575538215420965066507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605050358810280643377671 907575538215420965066507)
          ·
            refine ⟨1361363307323131447599761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907575538215420965066507 1361363307323131447599761)
            ·
              refine ⟨1021022480492348585699821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361363307323131447599761 1021022480492348585699821)
              ·
                refine ⟨382883430184630719637433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1021022480492348585699821 382883430184630719637433)
                ·
                  refine ⟨287162572638473039728075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382883430184630719637433 287162572638473039728075)
                  ·
                    rfl

theorem cell20_629153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_629153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629153 prefixEnd_629153 := by exact prefixLift 629153
  have htrace : WordTrace (prefixWord ++ tailWord_629153) baseStart_629153 baseEnd_629153 := by
    simpa [prefixWord, tailWord_629153, baseEnd_629153] using wordTrace_append hprefix tailTrace_629153
  have hstable : (prefixWord ++ tailWord_629153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629153).length < 2 ^ (prefixWord ++ tailWord_629153).sum := by decide
  have hdescent : baseEnd_629153 < baseStart_629153 := by decide
  rcases family_descends (prefixWord ++ tailWord_629153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629157 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 2]
def baseStart_629157 : Nat := 118140960795 + 629157 * 2 ^ 59
def prefixEnd_629157 : Nat := 4983230072969 + 3 ^ 40 * 629157 * 2
def baseEnd_629157 : Nat := 287164398347466803594725

theorem tailTrace_629157 : CollatzResearch.WordTrace tailWord_629157 prefixEnd_629157 287164398347466803594725 := by
  unfold tailWord_629157
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947240981679115306061725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15298160654452743537374483 22947240981679115306061725)
  ·
    refine ⟨8605215368129668239773147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22947240981679115306061725 8605215368129668239773147)
    ·
      refine ⟨12907823052194502359659721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8605215368129668239773147 12907823052194502359659721)
      ·
        refine ⟨9680867289145876769744791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12907823052194502359659721 9680867289145876769744791)
        ·
          refine ⟨14521300933718815154617187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9680867289145876769744791 14521300933718815154617187)
          ·
            refine ⟨21781951400578222731925781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14521300933718815154617187 21781951400578222731925781)
            ·
              refine ⟨1021028971902104190559021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21781951400578222731925781 1021028971902104190559021)
              ·
                refine ⟨382885864463289071459633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1021028971902104190559021 382885864463289071459633)
                ·
                  refine ⟨287164398347466803594725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382885864463289071459633 287164398347466803594725)
                  ·
                    rfl

theorem cell20_629157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_629157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629157 prefixEnd_629157 := by exact prefixLift 629157
  have htrace : WordTrace (prefixWord ++ tailWord_629157) baseStart_629157 baseEnd_629157 := by
    simpa [prefixWord, tailWord_629157, baseEnd_629157] using wordTrace_append hprefix tailTrace_629157
  have hstable : (prefixWord ++ tailWord_629157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629157).length < 2 ^ (prefixWord ++ tailWord_629157).sum := by decide
  have hdescent : baseEnd_629157 < baseStart_629157 := by decide
  rcases family_descends (prefixWord ++ tailWord_629157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629229 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 2]
def baseStart_629229 : Nat := 118140960795 + 629229 * 2 ^ 59
def prefixEnd_629229 : Nat := 4983230072969 + 3 ^ 40 * 629229 * 2
def baseEnd_629229 : Nat := 287197261109354553194431

theorem tailTrace_629229 : CollatzResearch.WordTrace tailWord_629229 prefixEnd_629229 287197261109354553194431 := by
  unfold tailWord_629229
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949867037418271602682741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15299911358278847735121827 22949867037418271602682741)
  ·
    refine ⟨2151550034757962962751507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22949867037418271602682741 2151550034757962962751507)
    ·
      refine ⟨3227325052136944444127261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151550034757962962751507 3227325052136944444127261)
      ·
        refine ⟨1210246894551354166547723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3227325052136944444127261 1210246894551354166547723)
        ·
          refine ⟨1815370341827031249821585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210246894551354166547723 1815370341827031249821585)
          ·
            refine ⟨1361527756370273437366189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815370341827031249821585 1361527756370273437366189)
            ·
              refine ⟨510572908638852539012321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1361527756370273437366189 510572908638852539012321)
              ·
                refine ⟨382929681479139404259241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510572908638852539012321 382929681479139404259241)
                ·
                  refine ⟨287197261109354553194431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382929681479139404259241 287197261109354553194431)
                  ·
                    rfl

theorem cell20_629229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_629229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629229 prefixEnd_629229 := by exact prefixLift 629229
  have htrace : WordTrace (prefixWord ++ tailWord_629229) baseStart_629229 baseEnd_629229 := by
    simpa [prefixWord, tailWord_629229, baseEnd_629229] using wordTrace_append hprefix tailTrace_629229
  have hstable : (prefixWord ++ tailWord_629229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629229).length < 2 ^ (prefixWord ++ tailWord_629229).sum := by decide
  have hdescent : baseEnd_629229 < baseStart_629229 := by decide
  rcases family_descends (prefixWord ++ tailWord_629229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629278 : List Nat := [4, 3, 3, 10]
def baseStart_629278 : Nat := 118140960795 + 629278 * 2 ^ 59
def prefixEnd_629278 : Nat := 4983230072969 + 3 ^ 40 * 629278 * 2
def baseEnd_629278 : Nat := 1181973769730568561979

theorem tailTrace_629278 : CollatzResearch.WordTrace tailWord_629278 prefixEnd_629278 1181973769730568561979 := by
  unfold tailWord_629278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868956776780094121402061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15301102809493835314144325 2868956776780094121402061)
  ·
    refine ⟨1075858791292535295525773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2868956776780094121402061 1075858791292535295525773)
    ·
      refine ⟨403447046734700735822165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1075858791292535295525773 403447046734700735822165)
      ·
        refine ⟨1181973769730568561979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 403447046734700735822165 1181973769730568561979)
        ·
          rfl

theorem cell20_629278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 10].length) (baseStart_629278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629278 prefixEnd_629278 := by exact prefixLift 629278
  have htrace : WordTrace (prefixWord ++ tailWord_629278) baseStart_629278 baseEnd_629278 := by
    simpa [prefixWord, tailWord_629278, baseEnd_629278] using wordTrace_append hprefix tailTrace_629278
  have hstable : (prefixWord ++ tailWord_629278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629278).length < 2 ^ (prefixWord ++ tailWord_629278).sum := by decide
  have hdescent : baseEnd_629278 < baseStart_629278 := by decide
  rcases family_descends (prefixWord ++ tailWord_629278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629284 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_629284 : Nat := 118140960795 + 629284 * 2 ^ 59
def prefixEnd_629284 : Nat := 4983230072969 + 3 ^ 40 * 629284 * 2
def baseEnd_629284 : Nat := 287222364608018806360873

theorem tailTrace_629284 : CollatzResearch.WordTrace tailWord_629284 prefixEnd_629284 287222364608018806360873 := by
  unfold tailWord_629284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475936526109507997967453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15301248701479343997289937 11475936526109507997967453)
  ·
    refine ⟨4303476197291065499237795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11475936526109507997967453 4303476197291065499237795)
    ·
      refine ⟨6455214295936598248856693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303476197291065499237795 6455214295936598248856693)
      ·
        refine ⟨605176340244056085830315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6455214295936598248856693 605176340244056085830315)
        ·
          refine ⟨907764510366084128745473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605176340244056085830315 907764510366084128745473)
          ·
            refine ⟨680823382774563096559105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907764510366084128745473 680823382774563096559105)
            ·
              refine ⟨510617537080922322419329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680823382774563096559105 510617537080922322419329)
              ·
                refine ⟨382963152810691741814497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510617537080922322419329 382963152810691741814497)
                ·
                  refine ⟨287222364608018806360873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382963152810691741814497 287222364608018806360873)
                  ·
                    rfl

theorem cell20_629284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_629284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629284 prefixEnd_629284 := by exact prefixLift 629284
  have htrace : WordTrace (prefixWord ++ tailWord_629284) baseStart_629284 baseEnd_629284 := by
    simpa [prefixWord, tailWord_629284, baseEnd_629284] using wordTrace_append hprefix tailTrace_629284
  have hstable : (prefixWord ++ tailWord_629284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629284).length < 2 ^ (prefixWord ++ tailWord_629284).sum := by decide
  have hdescent : baseEnd_629284 < baseStart_629284 := by decide
  rcases family_descends (prefixWord ++ tailWord_629284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629288 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_629288 : Nat := 118140960795 + 629288 * 2 ^ 59
def prefixEnd_629288 : Nat := 4983230072969 + 3 ^ 40 * 629288 * 2
def baseEnd_629288 : Nat := 287224190317012570227523

theorem tailTrace_629288 : CollatzResearch.WordTrace tailWord_629288 prefixEnd_629288 287224190317012570227523 := by
  unfold tailWord_629288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476009472102262339540259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15301345962803016452720345 11476009472102262339540259)
  ·
    refine ⟨17214014208153393509310389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11476009472102262339540259 17214014208153393509310389)
    ·
      refine ⟨1613813832014380641497849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17214014208153393509310389 1613813832014380641497849)
      ·
        refine ⟨1210360374010785481123387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613813832014380641497849 1210360374010785481123387)
        ·
          refine ⟨1815540561016178221685081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210360374010785481123387 1815540561016178221685081)
          ·
            refine ⟨1361655420762133666263811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815540561016178221685081 1361655420762133666263811)
            ·
              refine ⟨2042483131143200499395717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361655420762133666263811 2042483131143200499395717)
              ·
                refine ⟨382965587089350093636697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2042483131143200499395717 382965587089350093636697)
                ·
                  refine ⟨287224190317012570227523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382965587089350093636697 287224190317012570227523)
                  ·
                    rfl

theorem cell20_629288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_629288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629288 prefixEnd_629288 := by exact prefixLift 629288
  have htrace : WordTrace (prefixWord ++ tailWord_629288) baseStart_629288 baseEnd_629288 := by
    simpa [prefixWord, tailWord_629288, baseEnd_629288] using wordTrace_append hprefix tailTrace_629288
  have hstable : (prefixWord ++ tailWord_629288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629288).length < 2 ^ (prefixWord ++ tailWord_629288).sum := by decide
  have hdescent : baseEnd_629288 < baseStart_629288 := by decide
  rcases family_descends (prefixWord ++ tailWord_629288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629302 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_629302 : Nat := 118140960795 + 629302 * 2 ^ 59
def prefixEnd_629302 : Nat := 4983230072969 + 3 ^ 40 * 629302 * 2
def baseEnd_629302 : Nat := 287230580298490743760799

theorem tailTrace_629302 : CollatzResearch.WordTrace tailWord_629302 prefixEnd_629302 287230580298490743760799 := by
  unfold tailWord_629302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434533097884612816880635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15301686377435870046726773 1434533097884612816880635)
  ·
    refine ⟨2151799646826919225320953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434533097884612816880635 2151799646826919225320953)
    ·
      refine ⟨1613849735120189418990715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151799646826919225320953 1613849735120189418990715)
      ·
        refine ⟨2420774602680284128486073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613849735120189418990715 2420774602680284128486073)
        ·
          refine ⟨1815580952010213096364555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2420774602680284128486073 1815580952010213096364555)
          ·
            refine ⟨2723371428015319644546833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815580952010213096364555 2723371428015319644546833)
            ·
              refine ⟨2042528571011489733410125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723371428015319644546833 2042528571011489733410125)
              ·
                refine ⟨765948214129308650028797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2042528571011489733410125 765948214129308650028797)
                ·
                  refine ⟨287230580298490743760799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765948214129308650028797 287230580298490743760799)
                  ·
                    rfl

theorem cell20_629302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_629302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629302 prefixEnd_629302 := by exact prefixLift 629302
  have htrace : WordTrace (prefixWord ++ tailWord_629302) baseStart_629302 baseEnd_629302 := by
    simpa [prefixWord, tailWord_629302, baseEnd_629302] using wordTrace_append hprefix tailTrace_629302
  have hstable : (prefixWord ++ tailWord_629302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629302).length < 2 ^ (prefixWord ++ tailWord_629302).sum := by decide
  have hdescent : baseEnd_629302 < baseStart_629302 := by decide
  rcases family_descends (prefixWord ++ tailWord_629302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629320 : List Nat := [2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_629320 : Nat := 118140960795 + 629320 * 2 ^ 59
def prefixEnd_629320 : Nat := 4983230072969 + 3 ^ 40 * 629320 * 2
def baseEnd_629320 : Nat := 95746265329654227053575

theorem tailTrace_629320 : CollatzResearch.WordTrace tailWord_629320 prefixEnd_629320 95746265329654227053575 := by
  unfold tailWord_629320
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476593040044297072122707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15302124053392396096163609 11476593040044297072122707)
  ·
    refine ⟨17214889560066445608184061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11476593040044297072122707 17214889560066445608184061)
    ·
      refine ⟨6455583585024917103069023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17214889560066445608184061 6455583585024917103069023)
      ·
        refine ⟨9683375377537375654603535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6455583585024917103069023 9683375377537375654603535)
        ·
          refine ⟨14525063066306063481905303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9683375377537375654603535 14525063066306063481905303)
          ·
            refine ⟨21787594599459095222857955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14525063066306063481905303 21787594599459095222857955)
            ·
              refine ⟨32681391899188642834286933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21787594599459095222857955 32681391899188642834286933)
              ·
                refine ⟨95746265329654227053575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32681391899188642834286933 95746265329654227053575)
                ·
                  rfl

theorem cell20_629320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_629320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629320 prefixEnd_629320 := by exact prefixLift 629320
  have htrace : WordTrace (prefixWord ++ tailWord_629320) baseStart_629320 baseEnd_629320 := by
    simpa [prefixWord, tailWord_629320, baseEnd_629320] using wordTrace_append hprefix tailTrace_629320
  have hstable : (prefixWord ++ tailWord_629320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629320).length < 2 ^ (prefixWord ++ tailWord_629320).sum := by decide
  have hdescent : baseEnd_629320 < baseStart_629320 := by decide
  rcases family_descends (prefixWord ++ tailWord_629320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629402 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_629402 : Nat := 118140960795 + 629402 * 2 ^ 59
def prefixEnd_629402 : Nat := 4983230072969 + 3 ^ 40 * 629402 * 2
def baseEnd_629402 : Nat := 287276223023334840427057

theorem tailTrace_629402 : CollatzResearch.WordTrace tailWord_629402 prefixEnd_629402 287276223023334840427057 := by
  unfold tailWord_629402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739044216447880537182615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15304117910527681432486973 5739044216447880537182615)
  ·
    refine ⟨8608566324671820805773923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5739044216447880537182615 8608566324671820805773923)
    ·
      refine ⟨12912849487007731208660885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8608566324671820805773923 12912849487007731208660885)
      ·
        refine ⟨605289819703487400405979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12912849487007731208660885 605289819703487400405979)
        ·
          refine ⟨907934729555231100608969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605289819703487400405979 907934729555231100608969)
          ·
            refine ⟨680951047166423325456727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907934729555231100608969 680951047166423325456727)
            ·
              refine ⟨1021426570749634988185091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680951047166423325456727 1021426570749634988185091)
              ·
                refine ⟨1532139856124452482277637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021426570749634988185091 1532139856124452482277637)
                ·
                  refine ⟨287276223023334840427057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532139856124452482277637 287276223023334840427057)
                  ·
                    rfl

theorem cell20_629402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_629402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629402 prefixEnd_629402 := by exact prefixLift 629402
  have htrace : WordTrace (prefixWord ++ tailWord_629402) baseStart_629402 baseEnd_629402 := by
    simpa [prefixWord, tailWord_629402, baseEnd_629402] using wordTrace_append hprefix tailTrace_629402
  have hstable : (prefixWord ++ tailWord_629402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629402).length < 2 ^ (prefixWord ++ tailWord_629402).sum := by decide
  have hdescent : baseEnd_629402 < baseStart_629402 := by decide
  rcases family_descends (prefixWord ++ tailWord_629402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629434 : List Nat := [3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_629434 : Nat := 118140960795 + 629434 * 2 ^ 59
def prefixEnd_629434 : Nat := 4983230072969 + 3 ^ 40 * 629434 * 2
def baseEnd_629434 : Nat := 95763609565094983786753

theorem tailTrace_629434 : CollatzResearch.WordTrace tailWord_629434 prefixEnd_629434 95763609565094983786753 := by
  unfold tailWord_629434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739336000418897903473839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15304896001117061075930237 5739336000418897903473839)
  ·
    refine ⟨8609004000628346855210759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5739336000418897903473839 8609004000628346855210759)
    ·
      refine ⟨12913506000942520282816139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8609004000628346855210759 12913506000942520282816139)
      ·
        refine ⟨19370259001413780424224209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12913506000942520282816139 19370259001413780424224209)
        ·
          refine ⟨14527694251060335318168157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19370259001413780424224209 14527694251060335318168157)
          ·
            refine ⟨5447885344147625744313059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14527694251060335318168157 5447885344147625744313059)
            ·
              refine ⟨8171828016221438616469589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5447885344147625744313059 8171828016221438616469589)
              ·
                refine ⟨95763609565094983786753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8171828016221438616469589 95763609565094983786753)
                ·
                  rfl

theorem cell20_629434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_629434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629434 prefixEnd_629434 := by exact prefixLift 629434
  have htrace : WordTrace (prefixWord ++ tailWord_629434) baseStart_629434 baseEnd_629434 := by
    simpa [prefixWord, tailWord_629434, baseEnd_629434] using wordTrace_append hprefix tailTrace_629434
  have hstable : (prefixWord ++ tailWord_629434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629434).length < 2 ^ (prefixWord ++ tailWord_629434).sum := by decide
  have hdescent : baseEnd_629434 < baseStart_629434 := by decide
  rcases family_descends (prefixWord ++ tailWord_629434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629453 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 2]
def baseStart_629453 : Nat := 118140960795 + 629453 * 2 ^ 59
def prefixEnd_629453 : Nat := 4983230072969 + 3 ^ 40 * 629453 * 2
def baseEnd_629453 : Nat := 287299500813005329726849

theorem tailTrace_629453 : CollatzResearch.WordTrace tailWord_629453 prefixEnd_629453 287299500813005329726849 := by
  unfold tailWord_629453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22958036988606757858837013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15305357992404505239224675 22958036988606757858837013)
  ·
    refine ⟨1076157983840941774632985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22958036988606757858837013 1076157983840941774632985)
    ·
      refine ⟨807118487880706330974739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076157983840941774632985 807118487880706330974739)
      ·
        refine ⟨1210677731821059496462109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807118487880706330974739 1210677731821059496462109)
        ·
          refine ⟨454004149432897311173291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1210677731821059496462109 454004149432897311173291)
          ·
            refine ⟨681006224149345966759937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454004149432897311173291 681006224149345966759937)
            ·
              refine ⟨510754668112009475069953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681006224149345966759937 510754668112009475069953)
              ·
                refine ⟨383066001084007106302465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510754668112009475069953 383066001084007106302465)
                ·
                  refine ⟨287299500813005329726849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383066001084007106302465 287299500813005329726849)
                  ·
                    rfl

theorem cell20_629453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_629453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629453 prefixEnd_629453 := by exact prefixLift 629453
  have htrace : WordTrace (prefixWord ++ tailWord_629453) baseStart_629453 baseEnd_629453 := by
    simpa [prefixWord, tailWord_629453, baseEnd_629453] using wordTrace_append hprefix tailTrace_629453
  have hstable : (prefixWord ++ tailWord_629453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629453).length < 2 ^ (prefixWord ++ tailWord_629453).sum := by decide
  have hdescent : baseEnd_629453 < baseStart_629453 := by decide
  rcases family_descends (prefixWord ++ tailWord_629453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629465 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 4]
def baseStart_629465 : Nat := 118140960795 + 629465 * 2 ^ 59
def prefixEnd_629465 : Nat := 4983230072969 + 3 ^ 40 * 629465 * 2
def baseEnd_629465 : Nat := 287304977939986621326799

theorem tailTrace_629465 : CollatzResearch.WordTrace tailWord_629465 prefixEnd_629465 287304977939986621326799 := by
  unfold tailWord_629465
  simp only [CollatzResearch.WordTrace]
  refine ⟨22958474664563283908273849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15305649776375522605515899 22958474664563283908273849)
  ·
    refine ⟨17218855998422462931205387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22958474664563283908273849 17218855998422462931205387)
    ·
      refine ⟨25828283997633694396808081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17218855998422462931205387 25828283997633694396808081)
      ·
        refine ⟨19371212998225270797606061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25828283997633694396808081 19371212998225270797606061)
        ·
          refine ⟨7264204874334476549102273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19371212998225270797606061 7264204874334476549102273)
          ·
            refine ⟨5448153655750857411826705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264204874334476549102273 5448153655750857411826705)
            ·
              refine ⟨4086115241813143058870029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5448153655750857411826705 4086115241813143058870029)
              ·
                refine ⟨1532293215679928647076261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4086115241813143058870029 1532293215679928647076261)
                ·
                  refine ⟨287304977939986621326799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532293215679928647076261 287304977939986621326799)
                  ·
                    rfl

theorem cell20_629465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_629465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629465 prefixEnd_629465 := by exact prefixLift 629465
  have htrace : WordTrace (prefixWord ++ tailWord_629465) baseStart_629465 baseEnd_629465 := by
    simpa [prefixWord, tailWord_629465, baseEnd_629465] using wordTrace_append hprefix tailTrace_629465
  have hstable : (prefixWord ++ tailWord_629465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629465).length < 2 ^ (prefixWord ++ tailWord_629465).sum := by decide
  have hdescent : baseEnd_629465 < baseStart_629465 := by decide
  rcases family_descends (prefixWord ++ tailWord_629465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629468 : List Nat := [2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_629468 : Nat := 118140960795 + 629468 * 2 ^ 59
def prefixEnd_629468 : Nat := 4983230072969 + 3 ^ 40 * 629468 * 2
def baseEnd_629468 : Nat := 95768782407243981408929

theorem tailTrace_629468 : CollatzResearch.WordTrace tailWord_629468 prefixEnd_629468 95768782407243981408929 := by
  unfold tailWord_629468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11479292041776207710316529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15305722722368276947088705 11479292041776207710316529)
  ·
    refine ⟨8609469031332155782737397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11479292041776207710316529 8609469031332155782737397)
    ·
      refine ⟨807137721687389604631631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8609469031332155782737397 807137721687389604631631)
      ·
        refine ⟨1210706582531084406947447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807137721687389604631631 1210706582531084406947447)
        ·
          refine ⟨1816059873796626610421171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210706582531084406947447 1816059873796626610421171)
          ·
            refine ⟨2724089810694939915631757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816059873796626610421171 2724089810694939915631757)
            ·
              refine ⟨1021533679010602468361909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2724089810694939915631757 1021533679010602468361909)
              ·
                refine ⟨95768782407243981408929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021533679010602468361909 95768782407243981408929)
                ·
                  rfl

theorem cell20_629468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_629468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629468 prefixEnd_629468 := by exact prefixLift 629468
  have htrace : WordTrace (prefixWord ++ tailWord_629468) baseStart_629468 baseEnd_629468 := by
    simpa [prefixWord, tailWord_629468, baseEnd_629468] using wordTrace_append hprefix tailTrace_629468
  have hstable : (prefixWord ++ tailWord_629468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629468).length < 2 ^ (prefixWord ++ tailWord_629468).sum := by decide
  have hdescent : baseEnd_629468 < baseStart_629468 := by decide
  rcases family_descends (prefixWord ++ tailWord_629468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629475 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_629475 : Nat := 118140960795 + 629475 * 2 ^ 59
def prefixEnd_629475 : Nat := 4983230072969 + 3 ^ 40 * 629475 * 2
def baseEnd_629475 : Nat := 287309542212471030993425

theorem tailTrace_629475 : CollatzResearch.WordTrace tailWord_629475 prefixEnd_629475 287309542212471030993425 := by
  unfold tailWord_629475
  simp only [CollatzResearch.WordTrace]
  refine ⟨22958839394527055616137879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15305892929684703744091919 22958839394527055616137879)
  ·
    refine ⟨34438259091790583424206819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22958839394527055616137879 34438259091790583424206819)
    ·
      refine ⟨51657388637685875136310229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34438259091790583424206819 51657388637685875136310229)
      ·
        refine ⟨1210720046195762698507271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 51657388637685875136310229 1210720046195762698507271)
        ·
          refine ⟨1816080069293644047760907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210720046195762698507271 1816080069293644047760907)
          ·
            refine ⟨2724120103940466071641361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816080069293644047760907 2724120103940466071641361)
            ·
              refine ⟨2043090077955349553731021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724120103940466071641361 2043090077955349553731021)
              ·
                refine ⟨766158779233256082649133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2043090077955349553731021 766158779233256082649133)
                ·
                  refine ⟨287309542212471030993425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766158779233256082649133 287309542212471030993425)
                  ·
                    rfl

theorem cell20_629475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_629475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629475 prefixEnd_629475 := by exact prefixLift 629475
  have htrace : WordTrace (prefixWord ++ tailWord_629475) baseStart_629475 baseEnd_629475 := by
    simpa [prefixWord, tailWord_629475, baseEnd_629475] using wordTrace_append hprefix tailTrace_629475
  have hstable : (prefixWord ++ tailWord_629475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629475).length < 2 ^ (prefixWord ++ tailWord_629475).sum := by decide
  have hdescent : baseEnd_629475 < baseStart_629475 := by decide
  rcases family_descends (prefixWord ++ tailWord_629475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629489 : List Nat := [1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_629489 : Nat := 118140960795 + 629489 * 2 ^ 59
def prefixEnd_629489 : Nat := 4983230072969 + 3 ^ 40 * 629489 * 2
def baseEnd_629489 : Nat := 95771977397983068175567

theorem tailTrace_629489 : CollatzResearch.WordTrace tailWord_629489 prefixEnd_629489 95771977397983068175567 := by
  unfold tailWord_629489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22959350016476336007147521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15306233344317557338098347 22959350016476336007147521)
  ·
    refine ⟨17219512512357252005360641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22959350016476336007147521 17219512512357252005360641)
    ·
      refine ⟨12914634384267939004020481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17219512512357252005360641 12914634384267939004020481)
      ·
        refine ⟨9685975788200954253015361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12914634384267939004020481 9685975788200954253015361)
        ·
          refine ⟨7264481841150715689761521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9685975788200954253015361 7264481841150715689761521)
          ·
            refine ⟨5448361380863036767321141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7264481841150715689761521 5448361380863036767321141)
            ·
              refine ⟨510783879455909696936357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5448361380863036767321141 510783879455909696936357)
              ·
                refine ⟨95771977397983068175567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510783879455909696936357 95771977397983068175567)
                ·
                  rfl

theorem cell20_629489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_629489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629489 prefixEnd_629489 := by exact prefixLift 629489
  have htrace : WordTrace (prefixWord ++ tailWord_629489) baseStart_629489 baseEnd_629489 := by
    simpa [prefixWord, tailWord_629489, baseEnd_629489] using wordTrace_append hprefix tailTrace_629489
  have hstable : (prefixWord ++ tailWord_629489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629489).length < 2 ^ (prefixWord ++ tailWord_629489).sum := by decide
  have hdescent : baseEnd_629489 < baseStart_629489 := by decide
  rcases family_descends (prefixWord ++ tailWord_629489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629541 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_629541 : Nat := 118140960795 + 629541 * 2 ^ 59
def prefixEnd_629541 : Nat := 4983230072969 + 3 ^ 40 * 629541 * 2
def baseEnd_629541 : Nat := 287339666410868134793155

theorem tailTrace_629541 : CollatzResearch.WordTrace tailWord_629541 prefixEnd_629541 287339666410868134793155 := by
  unfold tailWord_629541
  simp only [CollatzResearch.WordTrace]
  refine ⟨22961246612287948888040477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15307497741525299258693651 22961246612287948888040477)
  ·
    refine ⟨8610467479607980833015179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22961246612287948888040477 8610467479607980833015179)
    ·
      refine ⟨12915701219411971249522769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8610467479607980833015179 12915701219411971249522769)
      ·
        refine ⟨9686775914558978437142077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12915701219411971249522769 9686775914558978437142077)
        ·
          refine ⟨3632540967959616913928279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9686775914558978437142077 3632540967959616913928279)
          ·
            refine ⟨5448811451939425370892419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632540967959616913928279 5448811451939425370892419)
            ·
              refine ⟨8173217177909138056338629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448811451939425370892419 8173217177909138056338629)
              ·
                refine ⟨1532478220857963385563493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8173217177909138056338629 1532478220857963385563493)
                ·
                  refine ⟨287339666410868134793155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532478220857963385563493 287339666410868134793155)
                  ·
                    rfl

theorem cell20_629541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_629541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629541 prefixEnd_629541 := by exact prefixLift 629541
  have htrace : WordTrace (prefixWord ++ tailWord_629541) baseStart_629541 baseEnd_629541 := by
    simpa [prefixWord, tailWord_629541, baseEnd_629541] using wordTrace_append hprefix tailTrace_629541
  have hstable : (prefixWord ++ tailWord_629541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629541).length < 2 ^ (prefixWord ++ tailWord_629541).sum := by decide
  have hdescent : baseEnd_629541 < baseStart_629541 := by decide
  rcases family_descends (prefixWord ++ tailWord_629541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629548 : List Nat := [2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_629548 : Nat := 118140960795 + 629548 * 2 ^ 59
def prefixEnd_629548 : Nat := 4983230072969 + 3 ^ 40 * 629548 * 2
def baseEnd_629548 : Nat := 95780953800535740519931

theorem tailTrace_629548 : CollatzResearch.WordTrace tailWord_629548 prefixEnd_629548 95780953800535740519931 := by
  unfold tailWord_629548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480750961631294541772649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15307667948841726055696865 11480750961631294541772649)
  ·
    refine ⟨8610563221223470906329487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11480750961631294541772649 8610563221223470906329487)
    ·
      refine ⟨12915844831835206359494231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8610563221223470906329487 12915844831835206359494231)
      ·
        refine ⟨19373767247752809539241347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12915844831835206359494231 19373767247752809539241347)
        ·
          refine ⟨29060650871629214308862021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19373767247752809539241347 29060650871629214308862021)
          ·
            refine ⟨5448872038430477682911629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29060650871629214308862021 5448872038430477682911629)
            ·
              refine ⟨2043327014411429131091861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5448872038430477682911629 2043327014411429131091861)
              ·
                refine ⟨95780953800535740519931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2043327014411429131091861 95780953800535740519931)
                ·
                  rfl

theorem cell20_629548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_629548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629548 prefixEnd_629548 := by exact prefixLift 629548
  have htrace : WordTrace (prefixWord ++ tailWord_629548) baseStart_629548 baseEnd_629548 := by
    simpa [prefixWord, tailWord_629548, baseEnd_629548] using wordTrace_append hprefix tailTrace_629548
  have hstable : (prefixWord ++ tailWord_629548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629548).length < 2 ^ (prefixWord ++ tailWord_629548).sum := by decide
  have hdescent : baseEnd_629548 < baseStart_629548 := by decide
  rcases family_descends (prefixWord ++ tailWord_629548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629585 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 3]
def baseStart_629585 : Nat := 118140960795 + 629585 * 2 ^ 59
def prefixEnd_629585 : Nat := 4983230072969 + 3 ^ 40 * 629585 * 2
def baseEnd_629585 : Nat := 287359749209799537326309

theorem tailTrace_629585 : CollatzResearch.WordTrace tailWord_629585 prefixEnd_629585 287359749209799537326309 := by
  unfold tailWord_629585
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962851424128544402642209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15308567616085696268428139 22962851424128544402642209)
  ·
    refine ⟨17222138568096408301981657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22962851424128544402642209 17222138568096408301981657)
    ·
      refine ⟨12916603926072306226486243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17222138568096408301981657 12916603926072306226486243)
      ·
        refine ⟨19374905889108459339729365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12916603926072306226486243 19374905889108459339729365)
        ·
          refine ⟨454099356775979515774907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19374905889108459339729365 454099356775979515774907)
          ·
            refine ⟨681149035163969273662361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454099356775979515774907 681149035163969273662361)
            ·
              refine ⟨510861776372976955246771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681149035163969273662361 510861776372976955246771)
              ·
                refine ⟨766292664559465432870157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510861776372976955246771 766292664559465432870157)
                ·
                  refine ⟨287359749209799537326309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766292664559465432870157 287359749209799537326309)
                  ·
                    rfl

theorem cell20_629585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_629585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629585 prefixEnd_629585 := by exact prefixLift 629585
  have htrace : WordTrace (prefixWord ++ tailWord_629585) baseStart_629585 baseEnd_629585 := by
    simpa [prefixWord, tailWord_629585, baseEnd_629585] using wordTrace_append hprefix tailTrace_629585
  have hstable : (prefixWord ++ tailWord_629585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629585).length < 2 ^ (prefixWord ++ tailWord_629585).sum := by decide
  have hdescent : baseEnd_629585 < baseStart_629585 := by decide
  rcases family_descends (prefixWord ++ tailWord_629585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629631 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_629631 : Nat := 118140960795 + 629631 * 2 ^ 59
def prefixEnd_629631 : Nat := 4983230072969 + 3 ^ 40 * 629631 * 2
def baseEnd_629631 : Nat := 287380744863227821792787

theorem tailTrace_629631 : CollatzResearch.WordTrace tailWord_629631 prefixEnd_629631 287380744863227821792787 := by
  unfold tailWord_629631
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964529181961894258816747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15309686121307929505877831 22964529181961894258816747)
  ·
    refine ⟨34446793772942841388225121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22964529181961894258816747 34446793772942841388225121)
    ·
      refine ⟨25835095329707131041168841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34446793772942841388225121 25835095329707131041168841)
      ·
        refine ⟨19376321497280348280876631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25835095329707131041168841 19376321497280348280876631)
        ·
          refine ⟨29064482245920522421314947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19376321497280348280876631 29064482245920522421314947)
          ·
            refine ⟨43596723368880783631972421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29064482245920522421314947 43596723368880783631972421)
            ·
              refine ⟨8174385631665146930994829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43596723368880783631972421 8174385631665146930994829)
              ·
                refine ⟨3065394611874430099123061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8174385631665146930994829 3065394611874430099123061)
                ·
                  refine ⟨287380744863227821792787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3065394611874430099123061 287380744863227821792787)
                  ·
                    rfl

theorem cell20_629631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_629631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629631 prefixEnd_629631 := by exact prefixLift 629631
  have htrace : WordTrace (prefixWord ++ tailWord_629631) baseStart_629631 baseEnd_629631 := by
    simpa [prefixWord, tailWord_629631, baseEnd_629631] using wordTrace_append hprefix tailTrace_629631
  have hstable : (prefixWord ++ tailWord_629631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629631).length < 2 ^ (prefixWord ++ tailWord_629631).sum := by decide
  have hdescent : baseEnd_629631 < baseStart_629631 := by decide
  rcases family_descends (prefixWord ++ tailWord_629631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629641 : List Nat := [1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_629641 : Nat := 118140960795 + 629641 * 2 ^ 59
def prefixEnd_629641 : Nat := 4983230072969 + 3 ^ 40 * 629641 * 2
def baseEnd_629641 : Nat := 95795103045237410486471

theorem tailTrace_629641 : CollatzResearch.WordTrace tailWord_629641 prefixEnd_629641 95795103045237410486471 := by
  unfold tailWord_629641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964893911925665966680777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15309929274617110644453851 22964893911925665966680777)
  ·
    refine ⟨17223670433944249475010583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22964893911925665966680777 17223670433944249475010583)
    ·
      refine ⟨25835505650916374212515875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17223670433944249475010583 25835505650916374212515875)
      ·
        refine ⟨38753258476374561318773813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25835505650916374212515875 38753258476374561318773813)
        ·
          refine ⟨3633117982160115123635045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38753258476374561318773813 3633117982160115123635045)
          ·
            refine ⟨681209621655021585681571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3633117982160115123635045 681209621655021585681571)
            ·
              refine ⟨1021814432482532378522357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681209621655021585681571 1021814432482532378522357)
              ·
                refine ⟨95795103045237410486471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021814432482532378522357 95795103045237410486471)
                ·
                  rfl

theorem cell20_629641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_629641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629641 prefixEnd_629641 := by exact prefixLift 629641
  have htrace : WordTrace (prefixWord ++ tailWord_629641) baseStart_629641 baseEnd_629641 := by
    simpa [prefixWord, tailWord_629641, baseEnd_629641] using wordTrace_append hprefix tailTrace_629641
  have hstable : (prefixWord ++ tailWord_629641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629641).length < 2 ^ (prefixWord ++ tailWord_629641).sum := by decide
  have hdescent : baseEnd_629641 < baseStart_629641 := by decide
  rcases family_descends (prefixWord ++ tailWord_629641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629654 : List Nat := [5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_629654 : Nat := 118140960795 + 629654 * 2 ^ 59
def prefixEnd_629654 : Nat := 4983230072969 + 3 ^ 40 * 629654 * 2
def baseEnd_629654 : Nat := 95797080896647321342009

theorem tailTrace_629654 : CollatzResearch.WordTrace tailWord_629654 prefixEnd_629654 95797080896647321342009 := by
  unfold tailWord_629654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435335503804910574181501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15310245373919046124602677 1435335503804910574181501)
  ·
    refine ⟨538250813926841465318063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1435335503804910574181501 538250813926841465318063)
    ·
      refine ⟨807376220890262197977095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538250813926841465318063 807376220890262197977095)
      ·
        refine ⟨1211064331335393296965643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807376220890262197977095 1211064331335393296965643)
        ·
          refine ⟨1816596497003089945448465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211064331335393296965643 1816596497003089945448465)
          ·
            refine ⟨1362447372752317459086349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816596497003089945448465 1362447372752317459086349)
            ·
              refine ⟨510917764782119047157381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362447372752317459086349 510917764782119047157381)
              ·
                refine ⟨95797080896647321342009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510917764782119047157381 95797080896647321342009)
                ·
                  rfl

theorem cell20_629654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_629654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629654 prefixEnd_629654 := by exact prefixLift 629654
  have htrace : WordTrace (prefixWord ++ tailWord_629654) baseStart_629654 baseEnd_629654 := by
    simpa [prefixWord, tailWord_629654, baseEnd_629654] using wordTrace_append hprefix tailTrace_629654
  have hstable : (prefixWord ++ tailWord_629654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629654).length < 2 ^ (prefixWord ++ tailWord_629654).sum := by decide
  have hdescent : baseEnd_629654 < baseStart_629654 := by decide
  rcases family_descends (prefixWord ++ tailWord_629654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629655 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_629655 : Nat := 118140960795 + 629655 * 2 ^ 59
def prefixEnd_629655 : Nat := 4983230072969 + 3 ^ 40 * 629655 * 2
def baseEnd_629655 : Nat := 287391699117190404992689

theorem tailTrace_629655 : CollatzResearch.WordTrace tailWord_629655 prefixEnd_629655 287391699117190404992689 := by
  unfold tailWord_629655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22965404533874946357690419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15310269689249964238460279 22965404533874946357690419)
  ·
    refine ⟨34448106800812419536535629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22965404533874946357690419 34448106800812419536535629)
    ·
      refine ⟨12918040050304657326200861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34448106800812419536535629 12918040050304657326200861)
      ·
        refine ⟨4844265018864246497325323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12918040050304657326200861 4844265018864246497325323)
        ·
          refine ⟨7266397528296369745987985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844265018864246497325323 7266397528296369745987985)
          ·
            refine ⟨5449798146222277309490989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7266397528296369745987985 5449798146222277309490989)
            ·
              refine ⟨2043674304833353991059121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5449798146222277309490989 2043674304833353991059121)
              ·
                refine ⟨1532755728625015493294341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043674304833353991059121 1532755728625015493294341)
                ·
                  refine ⟨287391699117190404992689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532755728625015493294341 287391699117190404992689)
                  ·
                    rfl

theorem cell20_629655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_629655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629655 prefixEnd_629655 := by exact prefixLift 629655
  have htrace : WordTrace (prefixWord ++ tailWord_629655) baseStart_629655 baseEnd_629655 := by
    simpa [prefixWord, tailWord_629655, baseEnd_629655] using wordTrace_append hprefix tailTrace_629655
  have hstable : (prefixWord ++ tailWord_629655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629655).length < 2 ^ (prefixWord ++ tailWord_629655).sum := by decide
  have hdescent : baseEnd_629655 < baseStart_629655 := by decide
  rcases family_descends (prefixWord ++ tailWord_629655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629658 : List Nat := [3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_629658 : Nat := 118140960795 + 629658 * 2 ^ 59
def prefixEnd_629658 : Nat := 4983230072969 + 3 ^ 40 * 629658 * 2
def baseEnd_629658 : Nat := 95797689466311909297559

theorem tailTrace_629658 : CollatzResearch.WordTrace tailWord_629658 prefixEnd_629658 95797689466311909297559 := by
  unfold tailWord_629658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741378488216019467512407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15310342635242718580033085 5741378488216019467512407)
  ·
    refine ⟨8612067732324029201268611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5741378488216019467512407 8612067732324029201268611)
    ·
      refine ⟨12918101598486043801902917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8612067732324029201268611 12918101598486043801902917)
      ·
        refine ⟨2422144049716133212856797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12918101598486043801902917 2422144049716133212856797)
        ·
          refine ⟨908304018643549954821299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2422144049716133212856797 908304018643549954821299)
          ·
            refine ⟨1362456027965324932231949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908304018643549954821299 1362456027965324932231949)
            ·
              refine ⟨510921010486996849586981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362456027965324932231949 510921010486996849586981)
              ·
                refine ⟨95797689466311909297559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510921010486996849586981 95797689466311909297559)
                ·
                  rfl

theorem cell20_629658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_629658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629658 prefixEnd_629658 := by exact prefixLift 629658
  have htrace : WordTrace (prefixWord ++ tailWord_629658) baseStart_629658 baseEnd_629658 := by
    simpa [prefixWord, tailWord_629658, baseEnd_629658] using wordTrace_append hprefix tailTrace_629658
  have hstable : (prefixWord ++ tailWord_629658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629658).length < 2 ^ (prefixWord ++ tailWord_629658).sum := by decide
  have hdescent : baseEnd_629658 < baseStart_629658 := by decide
  rcases family_descends (prefixWord ++ tailWord_629658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629709 : List Nat := [1, 6, 3, 1, 1, 2, 2, 4]
def baseStart_629709 : Nat := 118140960795 + 629709 * 2 ^ 59
def prefixEnd_629709 : Nat := 4983230072969 + 3 ^ 40 * 629709 * 2
def baseEnd_629709 : Nat := 95805448729535405730823

theorem tailTrace_629709 : CollatzResearch.WordTrace tailWord_629709 prefixEnd_629709 95805448729535405730823 := by
  unfold tailWord_629709
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967374075679313580156181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15311582717119542386770787 22967374075679313580156181)
  ·
    refine ⟨1076595659797467824069821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22967374075679313580156181 1076595659797467824069821)
    ·
      refine ⟨403723372424050434026183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1076595659797467824069821 403723372424050434026183)
      ·
        refine ⟨605585058636075651039275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403723372424050434026183 605585058636075651039275)
        ·
          refine ⟨908377587954113476558913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605585058636075651039275 908377587954113476558913)
          ·
            refine ⟨681283190965585107419185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908377587954113476558913 681283190965585107419185)
            ·
              refine ⟨510962393224188830564389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681283190965585107419185 510962393224188830564389)
              ·
                refine ⟨95805448729535405730823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510962393224188830564389 95805448729535405730823)
                ·
                  rfl

theorem cell20_629709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_629709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629709 prefixEnd_629709 := by exact prefixLift 629709
  have htrace : WordTrace (prefixWord ++ tailWord_629709) baseStart_629709 baseEnd_629709 := by
    simpa [prefixWord, tailWord_629709, baseEnd_629709] using wordTrace_append hprefix tailTrace_629709
  have hstable : (prefixWord ++ tailWord_629709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629709).length < 2 ^ (prefixWord ++ tailWord_629709).sum := by decide
  have hdescent : baseEnd_629709 < baseStart_629709 := by decide
  rcases family_descends (prefixWord ++ tailWord_629709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629717 : List Nat := [1, 3, 2, 3, 3, 1, 1, 6]
def baseStart_629717 : Nat := 118140960795 + 629717 * 2 ^ 59
def prefixEnd_629717 : Nat := 4983230072969 + 3 ^ 40 * 629717 * 2
def baseEnd_629717 : Nat := 95806665868864581641923

theorem tailTrace_629717 : CollatzResearch.WordTrace tailWord_629717 prefixEnd_629717 95806665868864581641923 := by
  unfold tailWord_629717
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967665859650330946447405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15311777239766887297631603 22967665859650330946447405)
  ·
    refine ⟨8612874697368874104917777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22967665859650330946447405 8612874697368874104917777)
    ·
      refine ⟨6459656023026655578688333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8612874697368874104917777 6459656023026655578688333)
      ·
        refine ⟨2422371008634995842008125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6459656023026655578688333 2422371008634995842008125)
        ·
          refine ⟨908389128238123440753047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2422371008634995842008125 908389128238123440753047)
          ·
            refine ⟨1362583692357185161129571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908389128238123440753047 1362583692357185161129571)
            ·
              refine ⟨2043875538535777741694357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362583692357185161129571 2043875538535777741694357)
              ·
                refine ⟨95806665868864581641923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2043875538535777741694357 95806665868864581641923)
                ·
                  rfl

theorem cell20_629717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 6].length) (baseStart_629717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629717 prefixEnd_629717 := by exact prefixLift 629717
  have htrace : WordTrace (prefixWord ++ tailWord_629717) baseStart_629717 baseEnd_629717 := by
    simpa [prefixWord, tailWord_629717, baseEnd_629717] using wordTrace_append hprefix tailTrace_629717
  have hstable : (prefixWord ++ tailWord_629717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629717).length < 2 ^ (prefixWord ++ tailWord_629717).sum := by decide
  have hdescent : baseEnd_629717 < baseStart_629717 := by decide
  rcases family_descends (prefixWord ++ tailWord_629717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629738 : List Nat := [3, 1, 3, 1, 2, 2, 8]
def baseStart_629738 : Nat := 118140960795 + 629738 * 2 ^ 59
def prefixEnd_629738 : Nat := 4983230072969 + 3 ^ 40 * 629738 * 2
def baseEnd_629738 : Nat := 31936620286534556136187

theorem tailTrace_629738 : CollatzResearch.WordTrace tailWord_629738 prefixEnd_629738 31936620286534556136187 := by
  unfold tailWord_629738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742107948143562883240467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15312287861716167688641245 5742107948143562883240467)
  ·
    refine ⟨8613161922215344324860701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5742107948143562883240467 8613161922215344324860701)
    ·
      refine ⟨3229935720830754121822763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8613161922215344324860701 3229935720830754121822763)
      ·
        refine ⟨4844903581246131182734145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229935720830754121822763 4844903581246131182734145)
        ·
          refine ⟨3633677685934598387050609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844903581246131182734145 3633677685934598387050609)
          ·
            refine ⟨2725258264450948790287957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3633677685934598387050609 2725258264450948790287957)
            ·
              refine ⟨31936620286534556136187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2725258264450948790287957 31936620286534556136187)
              ·
                rfl

theorem cell20_629738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_629738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629738 prefixEnd_629738 := by exact prefixLift 629738
  have htrace : WordTrace (prefixWord ++ tailWord_629738) baseStart_629738 baseEnd_629738 := by
    simpa [prefixWord, tailWord_629738, baseEnd_629738] using wordTrace_append hprefix tailTrace_629738
  have hstable : (prefixWord ++ tailWord_629738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629738).length < 2 ^ (prefixWord ++ tailWord_629738).sum := by decide
  have hdescent : baseEnd_629738 < baseStart_629738 := by decide
  rcases family_descends (prefixWord ++ tailWord_629738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629758 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_629758 : Nat := 118140960795 + 629758 * 2 ^ 59
def prefixEnd_629758 : Nat := 4983230072969 + 3 ^ 40 * 629758 * 2
def baseEnd_629758 : Nat := 287438711123779824558935

theorem tailTrace_629758 : CollatzResearch.WordTrace tailWord_629758 prefixEnd_629758 287438711123779824558935 := by
  unfold tailWord_629758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871145156562724368586241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15312774168334529965793285 2871145156562724368586241)
  ·
    refine ⟨2153358867422043276439681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2871145156562724368586241 2153358867422043276439681)
    ·
      refine ⟨1615019150566532457329761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2153358867422043276439681 1615019150566532457329761)
      ·
        refine ⟨1211264362924899342997321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615019150566532457329761 1211264362924899342997321)
        ·
          refine ⟨908448272193674507247991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211264362924899342997321 908448272193674507247991)
          ·
            refine ⟨1362672408290511760871987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908448272193674507247991 1362672408290511760871987)
            ·
              refine ⟨2044008612435767641307981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362672408290511760871987 2044008612435767641307981)
              ·
                refine ⟨766503229663412865490493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2044008612435767641307981 766503229663412865490493)
                ·
                  refine ⟨287438711123779824558935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766503229663412865490493 287438711123779824558935)
                  ·
                    rfl

theorem cell20_629758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_629758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629758 prefixEnd_629758 := by exact prefixLift 629758
  have htrace : WordTrace (prefixWord ++ tailWord_629758) baseStart_629758 baseEnd_629758 := by
    simpa [prefixWord, tailWord_629758, baseEnd_629758] using wordTrace_append hprefix tailTrace_629758
  have hstable : (prefixWord ++ tailWord_629758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629758).length < 2 ^ (prefixWord ++ tailWord_629758).sum := by decide
  have hdescent : baseEnd_629758 < baseStart_629758 := by decide
  rcases family_descends (prefixWord ++ tailWord_629758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629786 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_629786 : Nat := 118140960795 + 629786 * 2 ^ 59
def prefixEnd_629786 : Nat := 4983230072969 + 3 ^ 40 * 629786 * 2
def baseEnd_629786 : Nat := 287451491086736171625487

theorem tailTrace_629786 : CollatzResearch.WordTrace tailWord_629786 prefixEnd_629786 287451491086736171625487 := by
  unfold tailWord_629786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742545624100088932677303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15313454997600237153806141 5742545624100088932677303)
  ·
    refine ⟨8613818436150133399015955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5742545624100088932677303 8613818436150133399015955)
    ·
      refine ⟨12920727654225200098523933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8613818436150133399015955 12920727654225200098523933)
      ·
        refine ⟨4845272870334450036946475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12920727654225200098523933 4845272870334450036946475)
        ·
          refine ⟨7267909305501675055419713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845272870334450036946475 7267909305501675055419713)
          ·
            refine ⟨5450931979126256291564785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7267909305501675055419713 5450931979126256291564785)
            ·
              refine ⟨4088198984344692218673589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5450931979126256291564785 4088198984344692218673589)
              ·
                refine ⟨383268654782314895500649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4088198984344692218673589 383268654782314895500649)
                ·
                  refine ⟨287451491086736171625487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383268654782314895500649 287451491086736171625487)
                  ·
                    rfl

theorem cell20_629786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_629786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629786 prefixEnd_629786 := by exact prefixLift 629786
  have htrace : WordTrace (prefixWord ++ tailWord_629786) baseStart_629786 baseEnd_629786 := by
    simpa [prefixWord, tailWord_629786, baseEnd_629786] using wordTrace_append hprefix tailTrace_629786
  have hstable : (prefixWord ++ tailWord_629786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629786).length < 2 ^ (prefixWord ++ tailWord_629786).sum := by decide
  have hdescent : baseEnd_629786 < baseStart_629786 := by decide
  rcases family_descends (prefixWord ++ tailWord_629786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629799 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 2]
def baseStart_629799 : Nat := 118140960795 + 629799 * 2 ^ 59
def prefixEnd_629799 : Nat := 4983230072969 + 3 ^ 40 * 629799 * 2
def baseEnd_629799 : Nat := 287457424640965904192101

theorem tailTrace_629799 : CollatzResearch.WordTrace tailWord_629799 prefixEnd_629799 287457424640965904192101 := by
  unfold tailWord_629799
  simp only [CollatzResearch.WordTrace]
  refine ⟨22970656645353258950932451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15313771096902172633954967 22970656645353258950932451)
  ·
    refine ⟨34455984968029888426398677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22970656645353258950932451 34455984968029888426398677)
    ·
      refine ⟨807562147688200509993719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34455984968029888426398677 807562147688200509993719)
      ·
        refine ⟨1211343221532300764990579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807562147688200509993719 1211343221532300764990579)
        ·
          refine ⟨1817014832298451147485869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211343221532300764990579 1817014832298451147485869)
          ·
            refine ⟨681380562111919180307201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1817014832298451147485869 681380562111919180307201)
            ·
              refine ⟨511035421583939385230401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681380562111919180307201 511035421583939385230401)
              ·
                refine ⟨383276566187954538922801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511035421583939385230401 383276566187954538922801)
                ·
                  refine ⟨287457424640965904192101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383276566187954538922801 287457424640965904192101)
                  ·
                    rfl

theorem cell20_629799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2].length) (baseStart_629799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629799 prefixEnd_629799 := by exact prefixLift 629799
  have htrace : WordTrace (prefixWord ++ tailWord_629799) baseStart_629799 baseEnd_629799 := by
    simpa [prefixWord, tailWord_629799, baseEnd_629799] using wordTrace_append hprefix tailTrace_629799
  have hstable : (prefixWord ++ tailWord_629799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629799).length < 2 ^ (prefixWord ++ tailWord_629799).sum := by decide
  have hdescent : baseEnd_629799 < baseStart_629799 := by decide
  rcases family_descends (prefixWord ++ tailWord_629799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629831 : List Nat := [1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_629831 : Nat := 118140960795 + 629831 * 2 ^ 59
def prefixEnd_629831 : Nat := 4983230072969 + 3 ^ 40 * 629831 * 2
def baseEnd_629831 : Nat := 95824010104305338375101

theorem tailTrace_629831 : CollatzResearch.WordTrace tailWord_629831 prefixEnd_629831 95824010104305338375101 := by
  unfold tailWord_629831
  simp only [CollatzResearch.WordTrace]
  refine ⟨22971823781237328416097347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15314549187491552277398231 22971823781237328416097347)
  ·
    refine ⟨34457735671855992624146021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22971823781237328416097347 34457735671855992624146021)
    ·
      refine ⟨6460825438472998617027379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34457735671855992624146021 6460825438472998617027379)
      ·
        refine ⟨9691238157709497925541069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6460825438472998617027379 9691238157709497925541069)
        ·
          refine ⟨3634214309141061722077901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9691238157709497925541069 3634214309141061722077901)
          ·
            refine ⟨1362830365927898145779213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3634214309141061722077901 1362830365927898145779213)
            ·
              refine ⟨511061387222961804667205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362830365927898145779213 511061387222961804667205)
              ·
                refine ⟨95824010104305338375101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511061387222961804667205 95824010104305338375101)
                ·
                  rfl

theorem cell20_629831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_629831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629831 prefixEnd_629831 := by exact prefixLift 629831
  have htrace : WordTrace (prefixWord ++ tailWord_629831) baseStart_629831 baseEnd_629831 := by
    simpa [prefixWord, tailWord_629831, baseEnd_629831] using wordTrace_append hprefix tailTrace_629831
  have hstable : (prefixWord ++ tailWord_629831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629831).length < 2 ^ (prefixWord ++ tailWord_629831).sum := by decide
  have hdescent : baseEnd_629831 < baseStart_629831 := by decide
  rcases family_descends (prefixWord ++ tailWord_629831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629852 : List Nat := [2, 2, 4, 1, 1, 1, 9]
def baseStart_629852 : Nat := 118140960795 + 629852 * 2 ^ 59
def prefixEnd_629852 : Nat := 4983230072969 + 3 ^ 40 * 629852 * 2
def baseEnd_629852 : Nat := 31942401698348141713913

theorem tailTrace_629852 : CollatzResearch.WordTrace tailWord_629852 prefixEnd_629852 31942401698348141713913 := by
  unfold tailWord_629852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11486294857080624501305905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15315059809440832668407873 11486294857080624501305905)
  ·
    refine ⟨8614721142810468375979429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11486294857080624501305905 8614721142810468375979429)
    ·
      refine ⟨1615260214276962820496143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8614721142810468375979429 1615260214276962820496143)
      ·
        refine ⟨2422890321415444230744215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615260214276962820496143 2422890321415444230744215)
        ·
          refine ⟨3634335482123166346116323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422890321415444230744215 3634335482123166346116323)
          ·
            refine ⟨5451503223184749519174485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634335482123166346116323 5451503223184749519174485)
            ·
              refine ⟨31942401698348141713913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5451503223184749519174485 31942401698348141713913)
              ·
                rfl

theorem cell20_629852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 9].length) (baseStart_629852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629852 prefixEnd_629852 := by exact prefixLift 629852
  have htrace : WordTrace (prefixWord ++ tailWord_629852) baseStart_629852 baseEnd_629852 := by
    simpa [prefixWord, tailWord_629852, baseEnd_629852] using wordTrace_append hprefix tailTrace_629852
  have hstable : (prefixWord ++ tailWord_629852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629852).length < 2 ^ (prefixWord ++ tailWord_629852).sum := by decide
  have hdescent : baseEnd_629852 < baseStart_629852 := by decide
  rcases family_descends (prefixWord ++ tailWord_629852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629896 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_629896 : Nat := 118140960795 + 629896 * 2 ^ 59
def prefixEnd_629896 : Nat := 4983230072969 + 3 ^ 40 * 629896 * 2
def baseEnd_629896 : Nat := 287501698084064677958371

theorem tailTrace_629896 : CollatzResearch.WordTrace tailWord_629896 prefixEnd_629896 287501698084064677958371 := by
  unfold tailWord_629896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487097263000922258606771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15316129684001229678142361 11487097263000922258606771)
  ·
    refine ⟨17230645894501383387910157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11487097263000922258606771 17230645894501383387910157)
    ·
      refine ⟨6461492210438018770466309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17230645894501383387910157 6461492210438018770466309)
      ·
        refine ⟨1211529789457128519462433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6461492210438018770466309 1211529789457128519462433)
        ·
          refine ⟨908647342092846389596825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211529789457128519462433 908647342092846389596825)
          ·
            refine ⟨681485506569634792197619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908647342092846389596825 681485506569634792197619)
            ·
              refine ⟨1022228259854452188296429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681485506569634792197619 1022228259854452188296429)
              ·
                refine ⟨383335597445419570611161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022228259854452188296429 383335597445419570611161)
                ·
                  refine ⟨287501698084064677958371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383335597445419570611161 287501698084064677958371)
                  ·
                    rfl

theorem cell20_629896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_629896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629896 prefixEnd_629896 := by exact prefixLift 629896
  have htrace : WordTrace (prefixWord ++ tailWord_629896) baseStart_629896 baseEnd_629896 := by
    simpa [prefixWord, tailWord_629896, baseEnd_629896] using wordTrace_append hprefix tailTrace_629896
  have hstable : (prefixWord ++ tailWord_629896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629896).length < 2 ^ (prefixWord ++ tailWord_629896).sum := by decide
  have hdescent : baseEnd_629896 < baseStart_629896 := by decide
  rcases family_descends (prefixWord ++ tailWord_629896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629897 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_629897 : Nat := 118140960795 + 629897 * 2 ^ 59
def prefixEnd_629897 : Nat := 4983230072969 + 3 ^ 40 * 629897 * 2
def baseEnd_629897 : Nat := 287502154511313118925033

theorem tailTrace_629897 : CollatzResearch.WordTrace tailWord_629897 prefixEnd_629897 287502154511313118925033 := by
  unfold tailWord_629897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22974230998998221687999945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15316153999332147791999963 22974230998998221687999945)
  ·
    refine ⟨17230673249248666265999959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22974230998998221687999945 17230673249248666265999959)
    ·
      refine ⟨25846009873872999398999939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17230673249248666265999959 25846009873872999398999939)
      ·
        refine ⟨38769014810809499098499909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25846009873872999398999939 38769014810809499098499909)
        ·
          refine ⟨7269190277026781080968733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38769014810809499098499909 7269190277026781080968733)
          ·
            refine ⟨2725946353885042905363275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7269190277026781080968733 2725946353885042905363275)
            ·
              refine ⟨4088919530827564358044913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725946353885042905363275 4088919530827564358044913)
              ·
                refine ⟨3066689648120673268533685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088919530827564358044913 3066689648120673268533685)
                ·
                  refine ⟨287502154511313118925033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3066689648120673268533685 287502154511313118925033)
                  ·
                    rfl

theorem cell20_629897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_629897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629897 prefixEnd_629897 := by exact prefixLift 629897
  have htrace : WordTrace (prefixWord ++ tailWord_629897) baseStart_629897 baseEnd_629897 := by
    simpa [prefixWord, tailWord_629897, baseEnd_629897] using wordTrace_append hprefix tailTrace_629897
  have hstable : (prefixWord ++ tailWord_629897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629897).length < 2 ^ (prefixWord ++ tailWord_629897).sum := by decide
  have hdescent : baseEnd_629897 < baseStart_629897 := by decide
  rcases family_descends (prefixWord ++ tailWord_629897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629914 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_629914 : Nat := 118140960795 + 629914 * 2 ^ 59
def prefixEnd_629914 : Nat := 4983230072969 + 3 ^ 40 * 629914 * 2
def baseEnd_629914 : Nat := 287509913774536615358297

theorem tailTrace_629914 : CollatzResearch.WordTrace tailWord_629914 prefixEnd_629914 287509913774536615358297 := by
  unfold tailWord_629914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743712759984158397842199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15316567359957755727579197 5743712759984158397842199)
  ·
    refine ⟨8615569139976237596763299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5743712759984158397842199 8615569139976237596763299)
    ·
      refine ⟨12923353709964356395144949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8615569139976237596763299 12923353709964356395144949)
      ·
        refine ⟨1211564410309158412044839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12923353709964356395144949 1211564410309158412044839)
        ·
          refine ⟨1817346615463737618067259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211564410309158412044839 1817346615463737618067259)
          ·
            refine ⟨2726019923195606427100889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817346615463737618067259 2726019923195606427100889)
            ·
              refine ⟨2044514942396704820325667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726019923195606427100889 2044514942396704820325667)
              ·
                refine ⟨3066772413595057230488501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2044514942396704820325667 3066772413595057230488501)
                ·
                  refine ⟨287509913774536615358297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3066772413595057230488501 287509913774536615358297)
                  ·
                    rfl

theorem cell20_629914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_629914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629914 prefixEnd_629914 := by exact prefixLift 629914
  have htrace : WordTrace (prefixWord ++ tailWord_629914) baseStart_629914 baseEnd_629914 := by
    simpa [prefixWord, tailWord_629914, baseEnd_629914] using wordTrace_append hprefix tailTrace_629914
  have hstable : (prefixWord ++ tailWord_629914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629914).length < 2 ^ (prefixWord ++ tailWord_629914).sum := by decide
  have hdescent : baseEnd_629914 < baseStart_629914 := by decide
  rcases family_descends (prefixWord ++ tailWord_629914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629917 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 2]
def baseStart_629917 : Nat := 118140960795 + 629917 * 2 ^ 59
def prefixEnd_629917 : Nat := 4983230072969 + 3 ^ 40 * 629917 * 2
def baseEnd_629917 : Nat := 287511283056281938258285

theorem tailTrace_629917 : CollatzResearch.WordTrace tailWord_629917 prefixEnd_629917 287511283056281938258285 := by
  unfold tailWord_629917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22974960458925765103728005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15316640305950510069152003 22974960458925765103728005)
  ·
    refine ⟨4307805086048580956949001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22974960458925765103728005 4307805086048580956949001)
    ·
      refine ⟨3230853814536435717711751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4307805086048580956949001 3230853814536435717711751)
      ·
        refine ⟨4846280721804653576567627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230853814536435717711751 4846280721804653576567627)
        ·
          refine ⟨7269421082706980364851441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846280721804653576567627 7269421082706980364851441)
          ·
            refine ⟨5452065812030235273638581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7269421082706980364851441 5452065812030235273638581)
            ·
              refine ⟨511131169877834556903617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5452065812030235273638581 511131169877834556903617)
              ·
                refine ⟨383348377408375917677713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511131169877834556903617 383348377408375917677713)
                ·
                  refine ⟨287511283056281938258285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383348377408375917677713 287511283056281938258285)
                  ·
                    rfl

theorem cell20_629917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_629917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629917 prefixEnd_629917 := by exact prefixLift 629917
  have htrace : WordTrace (prefixWord ++ tailWord_629917) baseStart_629917 baseEnd_629917 := by
    simpa [prefixWord, tailWord_629917, baseEnd_629917] using wordTrace_append hprefix tailTrace_629917
  have hstable : (prefixWord ++ tailWord_629917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629917).length < 2 ^ (prefixWord ++ tailWord_629917).sum := by decide
  have hdescent : baseEnd_629917 < baseStart_629917 := by decide
  rcases family_descends (prefixWord ++ tailWord_629917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629965 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 3]
def baseStart_629965 : Nat := 118140960795 + 629965 * 2 ^ 59
def prefixEnd_629965 : Nat := 4983230072969 + 3 ^ 40 * 629965 * 2
def baseEnd_629965 : Nat := 287533191564207104658089

theorem tailTrace_629965 : CollatzResearch.WordTrace tailWord_629965 prefixEnd_629965 287533191564207104658089 := by
  unfold tailWord_629965
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976711162751869301475349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15317807441834579534316899 22976711162751869301475349)
  ·
    refine ⟨1077033335753993873506657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22976711162751869301475349 1077033335753993873506657)
    ·
      refine ⟨807775001815495405129993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1077033335753993873506657 807775001815495405129993)
      ·
        refine ⟨605831251361621553847495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 807775001815495405129993 605831251361621553847495)
        ·
          refine ⟨908746877042432330771243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605831251361621553847495 908746877042432330771243)
          ·
            refine ⟨1363120315563648496156865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908746877042432330771243 1363120315563648496156865)
            ·
              refine ⟨1022340236672736372117649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363120315563648496156865 1022340236672736372117649)
              ·
                refine ⟨766755177504552279088237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022340236672736372117649 766755177504552279088237)
                ·
                  refine ⟨287533191564207104658089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766755177504552279088237 287533191564207104658089)
                  ·
                    rfl

theorem cell20_629965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_629965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629965 prefixEnd_629965 := by exact prefixLift 629965
  have htrace : WordTrace (prefixWord ++ tailWord_629965) baseStart_629965 baseEnd_629965 := by
    simpa [prefixWord, tailWord_629965, baseEnd_629965] using wordTrace_append hprefix tailTrace_629965
  have hstable : (prefixWord ++ tailWord_629965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629965).length < 2 ^ (prefixWord ++ tailWord_629965).sum := by decide
  have hdescent : baseEnd_629965 < baseStart_629965 := by decide
  rcases family_descends (prefixWord ++ tailWord_629965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629966 : List Nat := [4, 1, 1, 1, 5, 8]
def baseStart_629966 : Nat := 118140960795 + 629966 * 2 ^ 59
def prefixEnd_629966 : Nat := 4983230072969 + 3 ^ 40 * 629966 * 2
def baseEnd_629966 : Nat := 10649394370053909097213

theorem tailTrace_629966 : CollatzResearch.WordTrace tailWord_629966 prefixEnd_629966 10649394370053909097213 := by
  unfold tailWord_629966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872093454468530809032719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15317831757165497648174501 2872093454468530809032719)
  ·
    refine ⟨4308140181702796213549079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2872093454468530809032719 4308140181702796213549079)
    ·
      refine ⟨6462210272554194320323619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4308140181702796213549079 6462210272554194320323619)
      ·
        refine ⟨9693315408831291480485429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462210272554194320323619 9693315408831291480485429)
        ·
          refine ⟨908748319577933576295509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9693315408831291480485429 908748319577933576295509)
          ·
            refine ⟨10649394370053909097213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 908748319577933576295509 10649394370053909097213)
            ·
              rfl

theorem cell20_629966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 8].length) (baseStart_629966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629966 prefixEnd_629966 := by exact prefixLift 629966
  have htrace : WordTrace (prefixWord ++ tailWord_629966) baseStart_629966 baseEnd_629966 := by
    simpa [prefixWord, tailWord_629966, baseEnd_629966] using wordTrace_append hprefix tailTrace_629966
  have hstable : (prefixWord ++ tailWord_629966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629966).length < 2 ^ (prefixWord ++ tailWord_629966).sum := by decide
  have hdescent : baseEnd_629966 < baseStart_629966 := by decide
  rcases family_descends (prefixWord ++ tailWord_629966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629972 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_629972 : Nat := 118140960795 + 629972 * 2 ^ 59
def prefixEnd_629972 : Nat := 4983230072969 + 3 ^ 40 * 629972 * 2
def baseEnd_629972 : Nat := 287536386554946191424727

theorem tailTrace_629972 : CollatzResearch.WordTrace tailWord_629972 prefixEnd_629972 287536386554946191424727 := by
  unfold tailWord_629972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11488483236863254748490085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15317977649151006331320113 11488483236863254748490085)
  ·
    refine ⟨2154090606911860265341891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11488483236863254748490085 2154090606911860265341891)
    ·
      refine ⟨3231135910367790398012837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154090606911860265341891 3231135910367790398012837)
      ·
        refine ⟨605837983193960699627407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3231135910367790398012837 605837983193960699627407)
        ·
          refine ⟨908756974790941049441111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605837983193960699627407 908756974790941049441111)
          ·
            refine ⟨1363135462186411574161667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908756974790941049441111 1363135462186411574161667)
            ·
              refine ⟨2044703193279617361242501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363135462186411574161667 2044703193279617361242501)
              ·
                refine ⟨383381848739928255232969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2044703193279617361242501 383381848739928255232969)
                ·
                  refine ⟨287536386554946191424727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383381848739928255232969 287536386554946191424727)
                  ·
                    rfl

theorem cell20_629972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_629972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629972 prefixEnd_629972 := by exact prefixLift 629972
  have htrace : WordTrace (prefixWord ++ tailWord_629972) baseStart_629972 baseEnd_629972 := by
    simpa [prefixWord, tailWord_629972, baseEnd_629972] using wordTrace_append hprefix tailTrace_629972
  have hstable : (prefixWord ++ tailWord_629972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629972).length < 2 ^ (prefixWord ++ tailWord_629972).sum := by decide
  have hdescent : baseEnd_629972 < baseStart_629972 := by decide
  rcases family_descends (prefixWord ++ tailWord_629972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629997 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_629997 : Nat := 118140960795 + 629997 * 2 ^ 59
def prefixEnd_629997 : Nat := 4983230072969 + 3 ^ 40 * 629997 * 2
def baseEnd_629997 : Nat := 287547797236157215591291

theorem tailTrace_629997 : CollatzResearch.WordTrace tailWord_629997 prefixEnd_629997 287547797236157215591291 := by
  unfold tailWord_629997
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977878298635938766640245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15318585532423959177760163 22977878298635938766640245)
  ·
    refine ⟨2154176090497119259372523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22977878298635938766640245 2154176090497119259372523)
    ·
      refine ⟨3231264135745678889058785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154176090497119259372523 3231264135745678889058785)
      ·
        refine ⟨2423448101809259166794089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3231264135745678889058785 2423448101809259166794089)
        ·
          refine ⟨1817586076356944375095567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2423448101809259166794089 1817586076356944375095567)
          ·
            refine ⟨2726379114535416562643351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817586076356944375095567 2726379114535416562643351)
            ·
              refine ⟨4089568671803124843965027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726379114535416562643351 4089568671803124843965027)
              ·
                refine ⟨6134353007704687265947541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089568671803124843965027 6134353007704687265947541)
                ·
                  refine ⟨287547797236157215591291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6134353007704687265947541 287547797236157215591291)
                  ·
                    rfl

theorem cell20_629997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_629997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_629997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_629997 prefixEnd_629997 := by exact prefixLift 629997
  have htrace : WordTrace (prefixWord ++ tailWord_629997) baseStart_629997 baseEnd_629997 := by
    simpa [prefixWord, tailWord_629997, baseEnd_629997] using wordTrace_append hprefix tailTrace_629997
  have hstable : (prefixWord ++ tailWord_629997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629997).length < 2 ^ (prefixWord ++ tailWord_629997).sum := by decide
  have hdescent : baseEnd_629997 < baseStart_629997 := by decide
  rcases family_descends (prefixWord ++ tailWord_629997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630024 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_630024 : Nat := 118140960795 + 630024 * 2 ^ 59
def prefixEnd_630024 : Nat := 4983230072969 + 3 ^ 40 * 630024 * 2
def baseEnd_630024 : Nat := 287560120771865121691181

theorem tailTrace_630024 : CollatzResearch.WordTrace tailWord_630024 prefixEnd_630024 287560120771865121691181 := by
  unfold tailWord_630024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489431534769061188936563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15319242046358748251915417 11489431534769061188936563)
  ·
    refine ⟨17234147302153591783404845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11489431534769061188936563 17234147302153591783404845)
    ·
      refine ⟨6462805238307596918776817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17234147302153591783404845 6462805238307596918776817)
      ·
        refine ⟨4847103928730697689082613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6462805238307596918776817 4847103928730697689082613)
        ·
          refine ⟨454415993318502908351495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4847103928730697689082613 454415993318502908351495)
          ·
            refine ⟨681623989977754362527243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454415993318502908351495 681623989977754362527243)
            ·
              refine ⟨1022435984966631543790865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681623989977754362527243 1022435984966631543790865)
              ·
                refine ⟨766826988724973657843149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022435984966631543790865 766826988724973657843149)
                ·
                  refine ⟨287560120771865121691181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766826988724973657843149 287560120771865121691181)
                  ·
                    rfl

theorem cell20_630024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_630024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630024 prefixEnd_630024 := by exact prefixLift 630024
  have htrace : WordTrace (prefixWord ++ tailWord_630024) baseStart_630024 baseEnd_630024 := by
    simpa [prefixWord, tailWord_630024, baseEnd_630024] using wordTrace_append hprefix tailTrace_630024
  have hstable : (prefixWord ++ tailWord_630024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630024).length < 2 ^ (prefixWord ++ tailWord_630024).sum := by decide
  have hdescent : baseEnd_630024 < baseStart_630024 := by decide
  rcases family_descends (prefixWord ++ tailWord_630024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630025 : List Nat := [1, 2, 1, 1, 3, 3, 9]
def baseStart_630025 : Nat := 118140960795 + 630025 * 2 ^ 59
def prefixEnd_630025 : Nat := 4983230072969 + 3 ^ 40 * 630025 * 2
def baseEnd_630025 : Nat := 31951175244345951406427

theorem tailTrace_630025 : CollatzResearch.WordTrace tailWord_630025 prefixEnd_630025 31951175244345951406427 := by
  unfold tailWord_630025
  simp only [CollatzResearch.WordTrace]
  refine ⟨22978899542534499548659529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15319266361689666365773019 22978899542534499548659529)
  ·
    refine ⟨17234174656900874661494647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22978899542534499548659529 17234174656900874661494647)
    ·
      refine ⟨25851261985351311992241971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17234174656900874661494647 25851261985351311992241971)
      ·
        refine ⟨38776892978026967988362957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25851261985351311992241971 38776892978026967988362957)
        ·
          refine ⟨14541334866760112995636109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38776892978026967988362957 14541334866760112995636109)
          ·
            refine ⟨5453000575035042373363541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14541334866760112995636109 5453000575035042373363541)
            ·
              refine ⟨31951175244345951406427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5453000575035042373363541 31951175244345951406427)
              ·
                rfl

theorem cell20_630025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_630025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630025 prefixEnd_630025 := by exact prefixLift 630025
  have htrace : WordTrace (prefixWord ++ tailWord_630025) baseStart_630025 baseEnd_630025 := by
    simpa [prefixWord, tailWord_630025, baseEnd_630025] using wordTrace_append hprefix tailTrace_630025
  have hstable : (prefixWord ++ tailWord_630025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630025).length < 2 ^ (prefixWord ++ tailWord_630025).sum := by decide
  have hdescent : baseEnd_630025 < baseStart_630025 := by decide
  rcases family_descends (prefixWord ++ tailWord_630025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630028 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_630028 : Nat := 118140960795 + 630028 * 2 ^ 59
def prefixEnd_630028 : Nat := 4983230072969 + 3 ^ 40 * 630028 * 2
def baseEnd_630028 : Nat := 287561946480858885557831

theorem tailTrace_630028 : CollatzResearch.WordTrace tailWord_630028 prefixEnd_630028 287561946480858885557831 := by
  unfold tailWord_630028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11489504480761815530509369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15319339307682420707345825 11489504480761815530509369)
  ·
    refine ⟨8617128360571361647882027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11489504480761815530509369 8617128360571361647882027)
    ·
      refine ⟨12925692540857042471823041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8617128360571361647882027 12925692540857042471823041)
      ·
        refine ⟨9694269405642781853867281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12925692540857042471823041 9694269405642781853867281)
        ·
          refine ⟨7270702054232086390400461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9694269405642781853867281 7270702054232086390400461)
          ·
            refine ⟨2726513270337032396400173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7270702054232086390400461 2726513270337032396400173)
            ·
              refine ⟨1022442476376387148650065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2726513270337032396400173 1022442476376387148650065)
              ·
                refine ⟨766831857282290361487549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022442476376387148650065 766831857282290361487549)
                ·
                  refine ⟨287561946480858885557831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766831857282290361487549 287561946480858885557831)
                  ·
                    rfl

theorem cell20_630028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_630028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630028 prefixEnd_630028 := by exact prefixLift 630028
  have htrace : WordTrace (prefixWord ++ tailWord_630028) baseStart_630028 baseEnd_630028 := by
    simpa [prefixWord, tailWord_630028, baseEnd_630028] using wordTrace_append hprefix tailTrace_630028
  have hstable : (prefixWord ++ tailWord_630028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630028).length < 2 ^ (prefixWord ++ tailWord_630028).sum := by decide
  have hdescent : baseEnd_630028 < baseStart_630028 := by decide
  rcases family_descends (prefixWord ++ tailWord_630028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630069 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 2]
def baseStart_630069 : Nat := 118140960795 + 630069 * 2 ^ 59
def prefixEnd_630069 : Nat := 4983230072969 + 3 ^ 40 * 630069 * 2
def baseEnd_630069 : Nat := 287580659998044965190997

theorem tailTrace_630069 : CollatzResearch.WordTrace tailWord_630069 prefixEnd_630069 287580659998044965190997 := by
  unfold tailWord_630069
  simp only [CollatzResearch.WordTrace]
  refine ⟨22980504354375095063261261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15320336236250063375507507 22980504354375095063261261)
  ·
    refine ⟨8617689132890660648722973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22980504354375095063261261 8617689132890660648722973)
    ·
      refine ⟨3231633424833997743271115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8617689132890660648722973 3231633424833997743271115)
      ·
        refine ⟨4847450137250996614906673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231633424833997743271115 4847450137250996614906673)
        ·
          refine ⟨3635587602938247461180005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4847450137250996614906673 3635587602938247461180005)
          ·
            refine ⟨681672675550921398971251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3635587602938247461180005 681672675550921398971251)
            ·
              refine ⟨1022509013326382098456877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681672675550921398971251 1022509013326382098456877)
              ·
                refine ⟨383440879997393286921329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022509013326382098456877 383440879997393286921329)
                ·
                  refine ⟨287580659998044965190997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383440879997393286921329 287580659998044965190997)
                  ·
                    rfl

theorem cell20_630069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_630069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630069 prefixEnd_630069 := by exact prefixLift 630069
  have htrace : WordTrace (prefixWord ++ tailWord_630069) baseStart_630069 baseEnd_630069 := by
    simpa [prefixWord, tailWord_630069, baseEnd_630069] using wordTrace_append hprefix tailTrace_630069
  have hstable : (prefixWord ++ tailWord_630069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630069).length < 2 ^ (prefixWord ++ tailWord_630069).sum := by decide
  have hdescent : baseEnd_630069 < baseStart_630069 := by decide
  rcases family_descends (prefixWord ++ tailWord_630069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630087 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_630087 : Nat := 118140960795 + 630087 * 2 ^ 59
def prefixEnd_630087 : Nat := 4983230072969 + 3 ^ 40 * 630087 * 2
def baseEnd_630087 : Nat := 287588875688516902590923

theorem tailTrace_630087 : CollatzResearch.WordTrace tailWord_630087 prefixEnd_630087 287588875688516902590923 := by
  unfold tailWord_630087
  simp only [CollatzResearch.WordTrace]
  refine ⟨22981160868309884137416515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15320773912206589424944343 22981160868309884137416515)
  ·
    refine ⟨34471741302464826206124773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22981160868309884137416515 34471741302464826206124773)
    ·
      refine ⟨6463451494212154913648395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34471741302464826206124773 6463451494212154913648395)
      ·
        refine ⟨9695177241318232370472593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6463451494212154913648395 9695177241318232370472593)
        ·
          refine ⟨7271382930988674277854445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9695177241318232370472593 7271382930988674277854445)
          ·
            refine ⟨2726768599120752854195417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7271382930988674277854445 2726768599120752854195417)
            ·
              refine ⟨2045076449340564640646563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726768599120752854195417 2045076449340564640646563)
              ·
                refine ⟨3067614674010846960969845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045076449340564640646563 3067614674010846960969845)
                ·
                  refine ⟨287588875688516902590923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3067614674010846960969845 287588875688516902590923)
                  ·
                    rfl

theorem cell20_630087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_630087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630087 prefixEnd_630087 := by exact prefixLift 630087
  have htrace : WordTrace (prefixWord ++ tailWord_630087) baseStart_630087 baseEnd_630087 := by
    simpa [prefixWord, tailWord_630087, baseEnd_630087] using wordTrace_append hprefix tailTrace_630087
  have hstable : (prefixWord ++ tailWord_630087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630087).length < 2 ^ (prefixWord ++ tailWord_630087).sum := by decide
  have hdescent : baseEnd_630087 < baseStart_630087 := by decide
  rcases family_descends (prefixWord ++ tailWord_630087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630145 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 2]
def baseStart_630145 : Nat := 118140960795 + 630145 * 2 ^ 59
def prefixEnd_630145 : Nat := 4983230072969 + 3 ^ 40 * 630145 * 2
def baseEnd_630145 : Nat := 287615348468926478657353

theorem tailTrace_630145 : CollatzResearch.WordTrace tailWord_630145 prefixEnd_630145 287615348468926478657353 := by
  unfold tailWord_630145
  simp only [CollatzResearch.WordTrace]
  refine ⟨22983276302099760043027889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15322184201399840028685259 22983276302099760043027889)
  ·
    refine ⟨17237457226574820032270917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22983276302099760043027889 17237457226574820032270917)
    ·
      refine ⟨3232023229982778756050797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17237457226574820032270917 3232023229982778756050797)
      ·
        refine ⟨1212008711243542033519049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3232023229982778756050797 1212008711243542033519049)
        ·
          refine ⟨909006533432656525139287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212008711243542033519049 909006533432656525139287)
          ·
            refine ⟨1363509800148984787708931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909006533432656525139287 1363509800148984787708931)
            ·
              refine ⟨2045264700223477181563397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363509800148984787708931 2045264700223477181563397)
              ·
                refine ⟨383487131291901971543137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2045264700223477181563397 383487131291901971543137)
                ·
                  refine ⟨287615348468926478657353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383487131291901971543137 287615348468926478657353)
                  ·
                    rfl

theorem cell20_630145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_630145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630145 prefixEnd_630145 := by exact prefixLift 630145
  have htrace : WordTrace (prefixWord ++ tailWord_630145) baseStart_630145 baseEnd_630145 := by
    simpa [prefixWord, tailWord_630145, baseEnd_630145] using wordTrace_append hprefix tailTrace_630145
  have hstable : (prefixWord ++ tailWord_630145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630145).length < 2 ^ (prefixWord ++ tailWord_630145).sum := by decide
  have hdescent : baseEnd_630145 < baseStart_630145 := by decide
  rcases family_descends (prefixWord ++ tailWord_630145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630173 : List Nat := [1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_630173 : Nat := 118140960795 + 630173 * 2 ^ 59
def prefixEnd_630173 : Nat := 4983230072969 + 3 ^ 40 * 630173 * 2
def baseEnd_630173 : Nat := 95876042810627608574635

theorem tailTrace_630173 : CollatzResearch.WordTrace tailWord_630173 prefixEnd_630173 95876042810627608574635 := by
  unfold tailWord_630173
  simp only [CollatzResearch.WordTrace]
  refine ⟨22984297545998320825047173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15322865030665547216698115 22984297545998320825047173)
  ·
    refine ⟨4309555789874685154696345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22984297545998320825047173 4309555789874685154696345)
    ·
      refine ⟨3232166842406013866022259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4309555789874685154696345 3232166842406013866022259)
      ·
        refine ⟨4848250263609020799033389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3232166842406013866022259 4848250263609020799033389)
        ·
          refine ⟨1818093848853382799637521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4848250263609020799033389 1818093848853382799637521)
          ·
            refine ⟨1363570386640037099728141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818093848853382799637521 1363570386640037099728141)
            ·
              refine ⟨511338894990013912398053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1363570386640037099728141 511338894990013912398053)
              ·
                refine ⟨95876042810627608574635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511338894990013912398053 95876042810627608574635)
                ·
                  rfl

theorem cell20_630173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_630173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630173 prefixEnd_630173 := by exact prefixLift 630173
  have htrace : WordTrace (prefixWord ++ tailWord_630173) baseStart_630173 baseEnd_630173 := by
    simpa [prefixWord, tailWord_630173, baseEnd_630173] using wordTrace_append hprefix tailTrace_630173
  have hstable : (prefixWord ++ tailWord_630173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630173).length < 2 ^ (prefixWord ++ tailWord_630173).sum := by decide
  have hdescent : baseEnd_630173 < baseStart_630173 := by decide
  rcases family_descends (prefixWord ++ tailWord_630173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630197 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_630197 : Nat := 118140960795 + 630197 * 2 ^ 59
def prefixEnd_630197 : Nat := 4983230072969 + 3 ^ 40 * 630197 * 2
def baseEnd_630197 : Nat := 287639082685845408923807

theorem tailTrace_630197 : CollatzResearch.WordTrace tailWord_630197 prefixEnd_630197 287639082685845408923807 := by
  unfold tailWord_630197
  simp only [CollatzResearch.WordTrace]
  refine ⟨22985172897911372923920845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15323448598607581949280563 22985172897911372923920845)
  ·
    refine ⟨8619439836716764846470317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22985172897911372923920845 8619439836716764846470317)
    ·
      refine ⟨3232289938768786817426369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8619439836716764846470317 3232289938768786817426369)
      ·
        refine ⟨2424217454076590113069777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3232289938768786817426369 2424217454076590113069777)
        ·
          refine ⟨1818163090557442584802333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2424217454076590113069777 1818163090557442584802333)
          ·
            refine ⟨681811158959040969300875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1818163090557442584802333 681811158959040969300875)
            ·
              refine ⟨1022716738438561453951313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681811158959040969300875 1022716738438561453951313)
              ·
                refine ⟨767037553828921090463485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022716738438561453951313 767037553828921090463485)
                ·
                  refine ⟨287639082685845408923807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767037553828921090463485 287639082685845408923807)
                  ·
                    rfl

theorem cell20_630197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_630197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630197 prefixEnd_630197 := by exact prefixLift 630197
  have htrace : WordTrace (prefixWord ++ tailWord_630197) baseStart_630197 baseEnd_630197 := by
    simpa [prefixWord, tailWord_630197, baseEnd_630197] using wordTrace_append hprefix tailTrace_630197
  have hstable : (prefixWord ++ tailWord_630197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630197).length < 2 ^ (prefixWord ++ tailWord_630197).sum := by decide
  have hdescent : baseEnd_630197 < baseStart_630197 := by decide
  rcases family_descends (prefixWord ++ tailWord_630197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630204 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_630204 : Nat := 118140960795 + 630204 * 2 ^ 59
def prefixEnd_630204 : Nat := 4983230072969 + 3 ^ 40 * 630204 * 2
def baseEnd_630204 : Nat := 287642277676584495690445

theorem tailTrace_630204 : CollatzResearch.WordTrace tailWord_630204 prefixEnd_630204 287642277676584495690445 := by
  unfold tailWord_630204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492714104443006559712833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15323618805924008746283777 11492714104443006559712833)
  ·
    refine ⟨8619535578332254919784625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11492714104443006559712833 8619535578332254919784625)
    ·
      refine ⟨6464651683749191189838469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8619535578332254919784625 6464651683749191189838469)
      ·
        refine ⟨1212122190702973348094713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6464651683749191189838469 1212122190702973348094713)
        ·
          refine ⟨909091643027230011071035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212122190702973348094713 909091643027230011071035)
          ·
            refine ⟨1363637464540845016606553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909091643027230011071035 1363637464540845016606553)
            ·
              refine ⟨1022728098405633762454915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363637464540845016606553 1022728098405633762454915)
              ·
                refine ⟨1534092147608450643682373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022728098405633762454915 1534092147608450643682373)
                ·
                  refine ⟨287642277676584495690445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534092147608450643682373 287642277676584495690445)
                  ·
                    rfl

theorem cell20_630204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_630204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630204 prefixEnd_630204 := by exact prefixLift 630204
  have htrace : WordTrace (prefixWord ++ tailWord_630204) baseStart_630204 baseEnd_630204 := by
    simpa [prefixWord, tailWord_630204, baseEnd_630204] using wordTrace_append hprefix tailTrace_630204
  have hstable : (prefixWord ++ tailWord_630204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630204).length < 2 ^ (prefixWord ++ tailWord_630204).sum := by decide
  have hdescent : baseEnd_630204 < baseStart_630204 := by decide
  rcases family_descends (prefixWord ++ tailWord_630204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630208 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_630208 : Nat := 118140960795 + 630208 * 2 ^ 59
def prefixEnd_630208 : Nat := 4983230072969 + 3 ^ 40 * 630208 * 2
def baseEnd_630208 : Nat := 287644103385578259557095

theorem tailTrace_630208 : CollatzResearch.WordTrace tailWord_630208 prefixEnd_630208 287644103385578259557095 := by
  unfold tailWord_630208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492787050435760901285639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15323716067247681201714185 11492787050435760901285639)
  ·
    refine ⟨17239180575653641351928459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492787050435760901285639 17239180575653641351928459)
    ·
      refine ⟨25858770863480462027892689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17239180575653641351928459 25858770863480462027892689)
      ·
        refine ⟨19394078147610346520919517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25858770863480462027892689 19394078147610346520919517)
        ·
          refine ⟨7272779305353879945344819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19394078147610346520919517 7272779305353879945344819)
          ·
            refine ⟨10909168958030819918017229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7272779305353879945344819 10909168958030819918017229)
            ·
              refine ⟨4090938359261557469256461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10909168958030819918017229 4090938359261557469256461)
              ·
                refine ⟨1534101884723084050971173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4090938359261557469256461 1534101884723084050971173)
                ·
                  refine ⟨287644103385578259557095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534101884723084050971173 287644103385578259557095)
                  ·
                    rfl

theorem cell20_630208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_630208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630208 prefixEnd_630208 := by exact prefixLift 630208
  have htrace : WordTrace (prefixWord ++ tailWord_630208) baseStart_630208 baseEnd_630208 := by
    simpa [prefixWord, tailWord_630208, baseEnd_630208] using wordTrace_append hprefix tailTrace_630208
  have hstable : (prefixWord ++ tailWord_630208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630208).length < 2 ^ (prefixWord ++ tailWord_630208).sum := by decide
  have hdescent : baseEnd_630208 < baseStart_630208 := by decide
  rcases family_descends (prefixWord ++ tailWord_630208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630215 : List Nat := [1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_630215 : Nat := 118140960795 + 630215 * 2 ^ 59
def prefixEnd_630215 : Nat := 4983230072969 + 3 ^ 40 * 630215 * 2
def baseEnd_630215 : Nat := 95882432792105782107911

theorem tailTrace_630215 : CollatzResearch.WordTrace tailWord_630215 prefixEnd_630215 95882432792105782107911 := by
  unfold tailWord_630215
  simp only [CollatzResearch.WordTrace]
  refine ⟨22985829411846161998076099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15323886274564107998717399 22985829411846161998076099)
  ·
    refine ⟨34478744117769242997114149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22985829411846161998076099 34478744117769242997114149)
    ·
      refine ⟨6464764522081733061958903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34478744117769242997114149 6464764522081733061958903)
      ·
        refine ⟨9697146783122599592938355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6464764522081733061958903 9697146783122599592938355)
        ·
          refine ⟨14545720174683899389407533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9697146783122599592938355 14545720174683899389407533)
          ·
            refine ⟨5454645065506462271027825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14545720174683899389407533 5454645065506462271027825)
            ·
              refine ⟨4090983799129846703270869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5454645065506462271027825 4090983799129846703270869)
              ·
                refine ⟨95882432792105782107911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4090983799129846703270869 95882432792105782107911)
                ·
                  rfl

theorem cell20_630215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_630215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630215 prefixEnd_630215 := by exact prefixLift 630215
  have htrace : WordTrace (prefixWord ++ tailWord_630215) baseStart_630215 baseEnd_630215 := by
    simpa [prefixWord, tailWord_630215, baseEnd_630215] using wordTrace_append hprefix tailTrace_630215
  have hstable : (prefixWord ++ tailWord_630215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630215).length < 2 ^ (prefixWord ++ tailWord_630215).sum := by decide
  have hdescent : baseEnd_630215 < baseStart_630215 := by decide
  rcases family_descends (prefixWord ++ tailWord_630215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630228 : List Nat := [2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_630228 : Nat := 118140960795 + 630228 * 2 ^ 59
def prefixEnd_630228 : Nat := 4983230072969 + 3 ^ 40 * 630228 * 2
def baseEnd_630228 : Nat := 95884410643515692963449

theorem tailTrace_630228 : CollatzResearch.WordTrace tailWord_630228 prefixEnd_630228 95884410643515692963449 := by
  unfold tailWord_630228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493151780399532609149669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15324202373866043478866225 11493151780399532609149669)
  ·
    refine ⟨2154965958824912364215563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11493151780399532609149669 2154965958824912364215563)
    ·
      refine ⟨3232448938237368546323345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154965958824912364215563 3232448938237368546323345)
      ·
        refine ⟨2424336703678026409742509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3232448938237368546323345 2424336703678026409742509)
        ·
          refine ⟨909126263879259903653441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2424336703678026409742509 909126263879259903653441)
          ·
            refine ⟨681844697909444927740081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909126263879259903653441 681844697909444927740081)
            ·
              refine ⟨511383523432083695805061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681844697909444927740081 511383523432083695805061)
              ·
                refine ⟨95884410643515692963449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511383523432083695805061 95884410643515692963449)
                ·
                  rfl

theorem cell20_630228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_630228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630228 prefixEnd_630228 := by exact prefixLift 630228
  have htrace : WordTrace (prefixWord ++ tailWord_630228) baseStart_630228 baseEnd_630228 := by
    simpa [prefixWord, tailWord_630228, baseEnd_630228] using wordTrace_append hprefix tailTrace_630228
  have hstable : (prefixWord ++ tailWord_630228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630228).length < 2 ^ (prefixWord ++ tailWord_630228).sum := by decide
  have hdescent : baseEnd_630228 < baseStart_630228 := by decide
  rcases family_descends (prefixWord ++ tailWord_630228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630232 : List Nat := [2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_630232 : Nat := 118140960795 + 630232 * 2 ^ 59
def prefixEnd_630232 : Nat := 4983230072969 + 3 ^ 40 * 630232 * 2
def baseEnd_630232 : Nat := 95885019213180280918999

theorem tailTrace_630232 : CollatzResearch.WordTrace tailWord_630232 prefixEnd_630232 95885019213180280918999 := by
  unfold tailWord_630232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493224726392286950722475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15324299635189715934296633 11493224726392286950722475)
  ·
    refine ⟨17239837089588430426083713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493224726392286950722475 17239837089588430426083713)
    ·
      refine ⟨12929877817191322819562785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17239837089588430426083713 12929877817191322819562785)
      ·
        refine ⟨9697408362893492114672089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12929877817191322819562785 9697408362893492114672089)
        ·
          refine ⟨7273056272170119086004067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9697408362893492114672089 7273056272170119086004067)
          ·
            refine ⟨10909584408255178629006101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7273056272170119086004067 10909584408255178629006101)
            ·
              refine ⟨511386769136961498234661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10909584408255178629006101 511386769136961498234661)
              ·
                refine ⟨95885019213180280918999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511386769136961498234661 95885019213180280918999)
                ·
                  rfl

theorem cell20_630232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_630232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630232 prefixEnd_630232 := by exact prefixLift 630232
  have htrace : WordTrace (prefixWord ++ tailWord_630232) baseStart_630232 baseEnd_630232 := by
    simpa [prefixWord, tailWord_630232, baseEnd_630232] using wordTrace_append hprefix tailTrace_630232
  have hstable : (prefixWord ++ tailWord_630232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630232).length < 2 ^ (prefixWord ++ tailWord_630232).sum := by decide
  have hdescent : baseEnd_630232 < baseStart_630232 := by decide
  rcases family_descends (prefixWord ++ tailWord_630232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630291 : List Nat := [1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_630291 : Nat := 118140960795 + 630291 * 2 ^ 59
def prefixEnd_630291 : Nat := 4983230072969 + 3 ^ 40 * 630291 * 2
def baseEnd_630291 : Nat := 95893995615732953263363

theorem tailTrace_630291 : CollatzResearch.WordTrace tailWord_630291 prefixEnd_630291 95893995615732953263363 := by
  unfold tailWord_630291
  simp only [CollatzResearch.WordTrace]
  refine ⟨22988601359570826977842727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15325734239713884651895151 22988601359570826977842727)
  ·
    refine ⟨34482902039356240466764091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22988601359570826977842727 34482902039356240466764091)
    ·
      refine ⟨51724353059034360700146137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34482902039356240466764091 51724353059034360700146137)
      ·
        refine ⟨38793264794275770525109603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51724353059034360700146137 38793264794275770525109603)
        ·
          refine ⟨58189897191413655787664405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38793264794275770525109603 58189897191413655787664405)
          ·
            refine ⟨2727651430847515115046769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58189897191413655787664405 2727651430847515115046769)
            ·
              refine ⟨2045738573135636336285077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2727651430847515115046769 2045738573135636336285077)
              ·
                refine ⟨95893995615732953263363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2045738573135636336285077 95893995615732953263363)
                ·
                  rfl

theorem cell20_630291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_630291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630291 prefixEnd_630291 := by exact prefixLift 630291
  have htrace : WordTrace (prefixWord ++ tailWord_630291) baseStart_630291 baseEnd_630291 := by
    simpa [prefixWord, tailWord_630291, baseEnd_630291] using wordTrace_append hprefix tailTrace_630291
  have hstable : (prefixWord ++ tailWord_630291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630291).length < 2 ^ (prefixWord ++ tailWord_630291).sum := by decide
  have hdescent : baseEnd_630291 < baseStart_630291 := by decide
  rcases family_descends (prefixWord ++ tailWord_630291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630322 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_630322 : Nat := 118140960795 + 630322 * 2 ^ 59
def prefixEnd_630322 : Nat := 4983230072969 + 3 ^ 40 * 630322 * 2
def baseEnd_630322 : Nat := 287696136091900529756629

theorem tailTrace_630322 : CollatzResearch.WordTrace tailWord_630322 prefixEnd_630322 287696136091900529756629 := by
  unfold tailWord_630322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747433005614629818055305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15326488014972346181480813 5747433005614629818055305)
  ·
    refine ⟨4310574754210972363541479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5747433005614629818055305 4310574754210972363541479)
    ·
      refine ⟨6465862131316458545312219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4310574754210972363541479 6465862131316458545312219)
      ·
        refine ⟨9698793196974687817968329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465862131316458545312219 9698793196974687817968329)
        ·
          refine ⟨7274094897731015863476247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9698793196974687817968329 7274094897731015863476247)
          ·
            refine ⟨10911142346596523795214371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7274094897731015863476247 10911142346596523795214371)
            ·
              refine ⟨16366713519894785692821557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10911142346596523795214371 16366713519894785692821557)
              ·
                refine ⟨1534379392490136158702021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16366713519894785692821557 1534379392490136158702021)
                ·
                  refine ⟨287696136091900529756629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534379392490136158702021 287696136091900529756629)
                  ·
                    rfl

theorem cell20_630322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_630322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630322 prefixEnd_630322 := by exact prefixLift 630322
  have htrace : WordTrace (prefixWord ++ tailWord_630322) baseStart_630322 baseEnd_630322 := by
    simpa [prefixWord, tailWord_630322, baseEnd_630322] using wordTrace_append hprefix tailTrace_630322
  have hstable : (prefixWord ++ tailWord_630322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630322).length < 2 ^ (prefixWord ++ tailWord_630322).sum := by decide
  have hdescent : baseEnd_630322 < baseStart_630322 := by decide
  rcases family_descends (prefixWord ++ tailWord_630322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630336 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_630336 : Nat := 118140960795 + 630336 * 2 ^ 59
def prefixEnd_630336 : Nat := 4983230072969 + 3 ^ 40 * 630336 * 2
def baseEnd_630336 : Nat := 287702526073378703289905

theorem tailTrace_630336 : CollatzResearch.WordTrace tailWord_630336 prefixEnd_630336 287702526073378703289905 := by
  unfold tailWord_630336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495121322203899831615431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15326828429605199775487241 11495121322203899831615431)
  ·
    refine ⟨17242681983305849747423147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11495121322203899831615431 17242681983305849747423147)
    ·
      refine ⟨25864022974958774621134721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17242681983305849747423147 25864022974958774621134721)
      ·
        refine ⟨19398017231219080965851041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25864022974958774621134721 19398017231219080965851041)
        ·
          refine ⟨14548512923414310724388281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19398017231219080965851041 14548512923414310724388281)
          ·
            refine ⟨10911384692560733043291211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14548512923414310724388281 10911384692560733043291211)
            ·
              refine ⟨16367077038841099564936817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10911384692560733043291211 16367077038841099564936817)
              ·
                refine ⟨12275307779130824673702613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16367077038841099564936817 12275307779130824673702613)
                ·
                  refine ⟨287702526073378703289905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12275307779130824673702613 287702526073378703289905)
                  ·
                    rfl

theorem cell20_630336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_630336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630336 prefixEnd_630336 := by exact prefixLift 630336
  have htrace : WordTrace (prefixWord ++ tailWord_630336) baseStart_630336 baseEnd_630336 := by
    simpa [prefixWord, tailWord_630336, baseEnd_630336] using wordTrace_append hprefix tailTrace_630336
  have hstable : (prefixWord ++ tailWord_630336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630336).length < 2 ^ (prefixWord ++ tailWord_630336).sum := by decide
  have hdescent : baseEnd_630336 < baseStart_630336 := by decide
  rcases family_descends (prefixWord ++ tailWord_630336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630346 : List Nat := [3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_630346 : Nat := 118140960795 + 630346 * 2 ^ 59
def prefixEnd_630346 : Nat := 4983230072969 + 3 ^ 40 * 630346 * 2
def baseEnd_630346 : Nat := 95902363448621037652177

theorem tailTrace_630346 : CollatzResearch.WordTrace tailWord_630346 prefixEnd_630346 95902363448621037652177 := by
  unfold tailWord_630346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747651843592892842773723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15327071582914380914063261 5747651843592892842773723)
  ·
    refine ⟨8621477765389339264160585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747651843592892842773723 8621477765389339264160585)
    ·
      refine ⟨6466108324042004448120439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8621477765389339264160585 6466108324042004448120439)
      ·
        refine ⟨9699162486063006672180659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466108324042004448120439 9699162486063006672180659)
        ·
          refine ⟨14548743729094510008270989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699162486063006672180659 14548743729094510008270989)
          ·
            refine ⟨5455778898410441253101621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14548743729094510008270989 5455778898410441253101621)
            ·
              refine ⟨511479271725978867478277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5455778898410441253101621 511479271725978867478277)
              ·
                refine ⟨95902363448621037652177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511479271725978867478277 95902363448621037652177)
                ·
                  rfl

theorem cell20_630346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_630346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630346 prefixEnd_630346 := by exact prefixLift 630346
  have htrace : WordTrace (prefixWord ++ tailWord_630346) baseStart_630346 baseEnd_630346 := by
    simpa [prefixWord, tailWord_630346, baseEnd_630346] using wordTrace_append hprefix tailTrace_630346
  have hstable : (prefixWord ++ tailWord_630346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630346).length < 2 ^ (prefixWord ++ tailWord_630346).sum := by decide
  have hdescent : baseEnd_630346 < baseStart_630346 := by decide
  rcases family_descends (prefixWord ++ tailWord_630346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630356 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_630356 : Nat := 118140960795 + 630356 * 2 ^ 59
def prefixEnd_630356 : Nat := 4983230072969 + 3 ^ 40 * 630356 * 2
def baseEnd_630356 : Nat := 287711654618347522623157

theorem tailTrace_630356 : CollatzResearch.WordTrace tailWord_630356 prefixEnd_630356 287711654618347522623157 := by
  unfold tailWord_630356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495486052167671539479461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15327314736223562052639281 11495486052167671539479461)
  ·
    refine ⟨2155403634781438413652399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11495486052167671539479461 2155403634781438413652399)
    ·
      refine ⟨3233105452172157620478599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155403634781438413652399 3233105452172157620478599)
      ·
        refine ⟨4849658178258236430717899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233105452172157620478599 4849658178258236430717899)
        ·
          refine ⟨7274487267387354646076849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849658178258236430717899 7274487267387354646076849)
          ·
            refine ⟨5455865450540515984557637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7274487267387354646076849 5455865450540515984557637)
            ·
              refine ⟨1022974771976346747104557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5455865450540515984557637 1022974771976346747104557)
              ·
                refine ⟨383615539491130030164209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022974771976346747104557 383615539491130030164209)
                ·
                  refine ⟨287711654618347522623157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383615539491130030164209 287711654618347522623157)
                  ·
                    rfl

theorem cell20_630356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_630356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630356 prefixEnd_630356 := by exact prefixLift 630356
  have htrace : WordTrace (prefixWord ++ tailWord_630356) baseStart_630356 baseEnd_630356 := by
    simpa [prefixWord, tailWord_630356, baseEnd_630356] using wordTrace_append hprefix tailTrace_630356
  have hstable : (prefixWord ++ tailWord_630356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630356).length < 2 ^ (prefixWord ++ tailWord_630356).sum := by decide
  have hdescent : baseEnd_630356 < baseStart_630356 := by decide
  rcases family_descends (prefixWord ++ tailWord_630356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630377 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 2]
def baseStart_630377 : Nat := 118140960795 + 630377 * 2 ^ 59
def prefixEnd_630377 : Nat := 4983230072969 + 3 ^ 40 * 630377 * 2
def baseEnd_630377 : Nat := 287721239590564782923071

theorem tailTrace_630377 : CollatzResearch.WordTrace tailWord_630377 prefixEnd_630377 287721239590564782923071 := by
  unfold tailWord_630377
  simp only [CollatzResearch.WordTrace]
  refine ⟨22991738037259263665473385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15327825358172842443648923 22991738037259263665473385)
  ·
    refine ⟨17243803527944447749105039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22991738037259263665473385 17243803527944447749105039)
    ·
      refine ⟨25865705291916671623657559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17243803527944447749105039 25865705291916671623657559)
      ·
        refine ⟨38798557937875007435486339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25865705291916671623657559 38798557937875007435486339)
        ·
          refine ⟨58197836906812511153229509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38798557937875007435486339 58197836906812511153229509)
          ·
            refine ⟨10912094420027345841230533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58197836906812511153229509 10912094420027345841230533)
            ·
              refine ⟨2046017703755127345230725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10912094420027345841230533 2046017703755127345230725)
              ·
                refine ⟨383628319454086377230761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2046017703755127345230725 383628319454086377230761)
                ·
                  refine ⟨287721239590564782923071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383628319454086377230761 287721239590564782923071)
                  ·
                    rfl

theorem cell20_630377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_630377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630377 prefixEnd_630377 := by exact prefixLift 630377
  have htrace : WordTrace (prefixWord ++ tailWord_630377) baseStart_630377 baseEnd_630377 := by
    simpa [prefixWord, tailWord_630377, baseEnd_630377] using wordTrace_append hprefix tailTrace_630377
  have hstable : (prefixWord ++ tailWord_630377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630377).length < 2 ^ (prefixWord ++ tailWord_630377).sum := by decide
  have hdescent : baseEnd_630377 < baseStart_630377 := by decide
  rcases family_descends (prefixWord ++ tailWord_630377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630401 : List Nat := [1, 2, 4, 2, 1, 4, 2, 4]
def baseStart_630401 : Nat := 118140960795 + 630401 * 2 ^ 59
def prefixEnd_630401 : Nat := 4983230072969 + 3 ^ 40 * 630401 * 2
def baseEnd_630401 : Nat := 95910731281509122040991

theorem tailTrace_630401 : CollatzResearch.WordTrace tailWord_630401 prefixEnd_630401 95910731281509122040991 := by
  unfold tailWord_630401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22992613389172315764347057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15328408926114877176231371 22992613389172315764347057)
  ·
    refine ⟨17244460041879236823260293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22992613389172315764347057 17244460041879236823260293)
    ·
      refine ⟨3233336257852356904361305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17244460041879236823260293 3233336257852356904361305)
      ·
        refine ⟨2425002193389267678270979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3233336257852356904361305 2425002193389267678270979)
        ·
          refine ⟨3637503290083901517406469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425002193389267678270979 3637503290083901517406469)
          ·
            refine ⟨682031866890731534513713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3637503290083901517406469 682031866890731534513713)
            ·
              refine ⟨511523900168048650885285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682031866890731534513713 511523900168048650885285)
              ·
                refine ⟨95910731281509122040991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511523900168048650885285 95910731281509122040991)
                ·
                  rfl

theorem cell20_630401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 4].length) (baseStart_630401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630401 prefixEnd_630401 := by exact prefixLift 630401
  have htrace : WordTrace (prefixWord ++ tailWord_630401) baseStart_630401 baseEnd_630401 := by
    simpa [prefixWord, tailWord_630401, baseEnd_630401] using wordTrace_append hprefix tailTrace_630401
  have hstable : (prefixWord ++ tailWord_630401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630401).length < 2 ^ (prefixWord ++ tailWord_630401).sum := by decide
  have hdescent : baseEnd_630401 < baseStart_630401 := by decide
  rcases family_descends (prefixWord ++ tailWord_630401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630405 : List Nat := [1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_630405 : Nat := 118140960795 + 630405 * 2 ^ 59
def prefixEnd_630405 : Nat := 4983230072969 + 3 ^ 40 * 630405 * 2
def baseEnd_630405 : Nat := 95911339851173709996541

theorem tailTrace_630405 : CollatzResearch.WordTrace tailWord_630405 prefixEnd_630405 95911339851173709996541 := by
  unfold tailWord_630405
  simp only [CollatzResearch.WordTrace]
  refine ⟨22992759281157824447492669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15328506187438549631661779 22992759281157824447492669)
  ·
    refine ⟨8622284730434184167809751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22992759281157824447492669 8622284730434184167809751)
    ·
      refine ⟨12933427095651276251714627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622284730434184167809751 12933427095651276251714627)
      ·
        refine ⟨19400140643476914377571941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12933427095651276251714627 19400140643476914377571941)
        ·
          refine ⟨3637526370651921445794739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19400140643476914377571941 3637526370651921445794739)
          ·
            refine ⟨5456289555977882168692109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637526370651921445794739 5456289555977882168692109)
            ·
              refine ⟨2046108583491705813259541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5456289555977882168692109 2046108583491705813259541)
              ·
                refine ⟨95911339851173709996541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2046108583491705813259541 95911339851173709996541)
                ·
                  rfl

theorem cell20_630405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_630405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630405 prefixEnd_630405 := by exact prefixLift 630405
  have htrace : WordTrace (prefixWord ++ tailWord_630405) baseStart_630405 baseEnd_630405 := by
    simpa [prefixWord, tailWord_630405, baseEnd_630405] using wordTrace_append hprefix tailTrace_630405
  have hstable : (prefixWord ++ tailWord_630405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630405).length < 2 ^ (prefixWord ++ tailWord_630405).sum := by decide
  have hdescent : baseEnd_630405 < baseStart_630405 := by decide
  rcases family_descends (prefixWord ++ tailWord_630405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630412 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_630412 : Nat := 118140960795 + 630412 * 2 ^ 59
def prefixEnd_630412 : Nat := 4983230072969 + 3 ^ 40 * 630412 * 2
def baseEnd_630412 : Nat := 287737214544260216756261

theorem tailTrace_630412 : CollatzResearch.WordTrace tailWord_630412 prefixEnd_630412 287737214544260216756261 := by
  unfold tailWord_630412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496507296066232321498745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15328676394754976428664993 11496507296066232321498745)
  ·
    refine ⟨8622380472049674241124059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11496507296066232321498745 8622380472049674241124059)
    ·
      refine ⟨12933570708074511361686089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622380472049674241124059 12933570708074511361686089)
      ·
        refine ⟨9700178031055883521264567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12933570708074511361686089 9700178031055883521264567)
        ·
          refine ⟨14550267046583825281896851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9700178031055883521264567 14550267046583825281896851)
          ·
            refine ⟨21825400569875737922845277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14550267046583825281896851 21825400569875737922845277)
            ·
              refine ⟨8184525213703401721066979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21825400569875737922845277 8184525213703401721066979)
              ·
                refine ⟨12276787820555102581600469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8184525213703401721066979 12276787820555102581600469)
                ·
                  refine ⟨287737214544260216756261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12276787820555102581600469 287737214544260216756261)
                  ·
                    rfl

theorem cell20_630412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_630412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630412 prefixEnd_630412 := by exact prefixLift 630412
  have htrace : WordTrace (prefixWord ++ tailWord_630412) baseStart_630412 baseEnd_630412 := by
    simpa [prefixWord, tailWord_630412, baseEnd_630412] using wordTrace_append hprefix tailTrace_630412
  have hstable : (prefixWord ++ tailWord_630412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630412).length < 2 ^ (prefixWord ++ tailWord_630412).sum := by decide
  have hdescent : baseEnd_630412 < baseStart_630412 := by decide
  rcases family_descends (prefixWord ++ tailWord_630412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630429 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_630429 : Nat := 118140960795 + 630429 * 2 ^ 59
def prefixEnd_630429 : Nat := 4983230072969 + 3 ^ 40 * 630429 * 2
def baseEnd_630429 : Nat := 287744973807483713189525

theorem tailTrace_630429 : CollatzResearch.WordTrace tailWord_630429 prefixEnd_630429 287744973807483713189525 := by
  unfold tailWord_630429
  simp only [CollatzResearch.WordTrace]
  refine ⟨22993634633070876546366341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15329089755380584364244227 22993634633070876546366341)
  ·
    refine ⟨4311306493700789352443689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22993634633070876546366341 4311306493700789352443689)
    ·
      refine ⟨3233479870275592014332767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4311306493700789352443689 3233479870275592014332767)
      ·
        refine ⟨4850219805413388021499151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233479870275592014332767 4850219805413388021499151)
        ·
          refine ⟨7275329708120082032248727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850219805413388021499151 7275329708120082032248727)
          ·
            refine ⟨10912994562180123048373091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275329708120082032248727 10912994562180123048373091)
            ·
              refine ⟨16369491843270184572559637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10912994562180123048373091 16369491843270184572559637)
              ·
                refine ⟨767319930153289901838733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16369491843270184572559637 767319930153289901838733)
                ·
                  refine ⟨287744973807483713189525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767319930153289901838733 287744973807483713189525)
                  ·
                    rfl

theorem cell20_630429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_630429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630429 prefixEnd_630429 := by exact prefixLift 630429
  have htrace : WordTrace (prefixWord ++ tailWord_630429) baseStart_630429 baseEnd_630429 := by
    simpa [prefixWord, tailWord_630429, baseEnd_630429] using wordTrace_append hprefix tailTrace_630429
  have hstable : (prefixWord ++ tailWord_630429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630429).length < 2 ^ (prefixWord ++ tailWord_630429).sum := by decide
  have hdescent : baseEnd_630429 < baseStart_630429 := by decide
  rcases family_descends (prefixWord ++ tailWord_630429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630484 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_630484 : Nat := 118140960795 + 630484 * 2 ^ 59
def prefixEnd_630484 : Nat := 4983230072969 + 3 ^ 40 * 630484 * 2
def baseEnd_630484 : Nat := 287770077306147966355967

theorem tailTrace_630484 : CollatzResearch.WordTrace tailWord_630484 prefixEnd_630484 287770077306147966355967 := by
  unfold tailWord_630484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497820323935810469809253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15330427098581080626412337 11497820323935810469809253)
  ·
    refine ⟨2155841310737964463089235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11497820323935810469809253 2155841310737964463089235)
    ·
      refine ⟨3233761966106946694633853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155841310737964463089235 3233761966106946694633853)
      ·
        refine ⟨1212660737290105010487695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3233761966106946694633853 1212660737290105010487695)
        ·
          refine ⟨1818991105935157515731543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212660737290105010487695 1818991105935157515731543)
          ·
            refine ⟨2728486658902736273597315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818991105935157515731543 2728486658902736273597315)
            ·
              refine ⟨4092729988354104410395973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728486658902736273597315 4092729988354104410395973)
              ·
                refine ⟨767386872816394576949245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4092729988354104410395973 767386872816394576949245)
                ·
                  refine ⟨287770077306147966355967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767386872816394576949245 287770077306147966355967)
                  ·
                    rfl

theorem cell20_630484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_630484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630484 prefixEnd_630484 := by exact prefixLift 630484
  have htrace : WordTrace (prefixWord ++ tailWord_630484) baseStart_630484 baseEnd_630484 := by
    simpa [prefixWord, tailWord_630484, baseEnd_630484] using wordTrace_append hprefix tailTrace_630484
  have hstable : (prefixWord ++ tailWord_630484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630484).length < 2 ^ (prefixWord ++ tailWord_630484).sum := by decide
  have hdescent : baseEnd_630484 < baseStart_630484 := by decide
  rcases family_descends (prefixWord ++ tailWord_630484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630529 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 2]
def baseStart_630529 : Nat := 118140960795 + 630529 * 2 ^ 59
def prefixEnd_630529 : Nat := 4983230072969 + 3 ^ 40 * 630529 * 2
def baseEnd_630529 : Nat := 287790616532327809855783

theorem tailTrace_630529 : CollatzResearch.WordTrace tailWord_630529 prefixEnd_630529 287790616532327809855783 := by
  unfold tailWord_630529
  simp only [CollatzResearch.WordTrace]
  refine ⟨22997281932708593625006641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15331521288472395750004427 22997281932708593625006641)
  ·
    refine ⟨17247961449531445218754981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22997281932708593625006641 17247961449531445218754981)
    ·
      refine ⟨3233992771787145978516559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17247961449531445218754981 3233992771787145978516559)
      ·
        refine ⟨4850989157680718967774839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233992771787145978516559 4850989157680718967774839)
        ·
          refine ⟨7276483736521078451662259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850989157680718967774839 7276483736521078451662259)
          ·
            refine ⟨10914725604781617677493389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276483736521078451662259 10914725604781617677493389)
            ·
              refine ⟨4093022101793106629060021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10914725604781617677493389 4093022101793106629060021)
              ·
                refine ⟨383720822043103746474377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4093022101793106629060021 383720822043103746474377)
                ·
                  refine ⟨287790616532327809855783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383720822043103746474377 287790616532327809855783)
                  ·
                    rfl

theorem cell20_630529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_630529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630529 prefixEnd_630529 := by exact prefixLift 630529
  have htrace : WordTrace (prefixWord ++ tailWord_630529) baseStart_630529 baseEnd_630529 := by
    simpa [prefixWord, tailWord_630529, baseEnd_630529] using wordTrace_append hprefix tailTrace_630529
  have hstable : (prefixWord ++ tailWord_630529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630529).length < 2 ^ (prefixWord ++ tailWord_630529).sum := by decide
  have hdescent : baseEnd_630529 < baseStart_630529 := by decide
  rcases family_descends (prefixWord ++ tailWord_630529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630546 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_630546 : Nat := 118140960795 + 630546 * 2 ^ 59
def prefixEnd_630546 : Nat := 4983230072969 + 3 ^ 40 * 630546 * 2
def baseEnd_630546 : Nat := 287798375795551306289047

theorem tailTrace_630546 : CollatzResearch.WordTrace tailWord_630546 prefixEnd_630546 287798375795551306289047 := by
  unfold tailWord_630546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5749475493411751382093873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15331934649098003685583661 5749475493411751382093873)
  ·
    refine ⟨4312106620058813536570405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5749475493411751382093873 4312106620058813536570405)
    ·
      refine ⟨808519991261027538106951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4312106620058813536570405 808519991261027538106951)
      ·
        refine ⟨1212779986891541307160427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808519991261027538106951 1212779986891541307160427)
        ·
          refine ⟨1819169980337311960740641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212779986891541307160427 1819169980337311960740641)
          ·
            refine ⟨1364377485252983970555481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819169980337311960740641 1364377485252983970555481)
            ·
              refine ⟨1023283113939737977916611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364377485252983970555481 1023283113939737977916611)
              ·
                refine ⟨1534924670909606966874917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023283113939737977916611 1534924670909606966874917)
                ·
                  refine ⟨287798375795551306289047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1534924670909606966874917 287798375795551306289047)
                  ·
                    rfl

theorem cell20_630546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_630546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630546 prefixEnd_630546 := by exact prefixLift 630546
  have htrace : WordTrace (prefixWord ++ tailWord_630546) baseStart_630546 baseEnd_630546 := by
    simpa [prefixWord, tailWord_630546, baseEnd_630546] using wordTrace_append hprefix tailTrace_630546
  have hstable : (prefixWord ++ tailWord_630546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630546).length < 2 ^ (prefixWord ++ tailWord_630546).sum := by decide
  have hdescent : baseEnd_630546 < baseStart_630546 := by decide
  rcases family_descends (prefixWord ++ tailWord_630546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630560 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_630560 : Nat := 118140960795 + 630560 * 2 ^ 59
def prefixEnd_630560 : Nat := 4983230072969 + 3 ^ 40 * 630560 * 2
def baseEnd_630560 : Nat := 287804765777029479822323

theorem tailTrace_630560 : CollatzResearch.WordTrace tailWord_630560 prefixEnd_630560 287804765777029479822323 := by
  unfold tailWord_630560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11499206297798142959692567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15332275063730857279590089 11499206297798142959692567)
  ·
    refine ⟨17248809446697214439538851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11499206297798142959692567 17248809446697214439538851)
    ·
      refine ⟨25873214170045821659308277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17248809446697214439538851 25873214170045821659308277)
      ·
        refine ⟨2425613828441795780560151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25873214170045821659308277 2425613828441795780560151)
        ·
          refine ⟨3638420742662693670840227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425613828441795780560151 3638420742662693670840227)
          ·
            refine ⟨5457631113994040506260341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638420742662693670840227 5457631113994040506260341)
            ·
              refine ⟨511652916936941297461907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5457631113994040506260341 511652916936941297461907)
              ·
                refine ⟨767479375405411946192861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511652916936941297461907 767479375405411946192861)
                ·
                  refine ⟨287804765777029479822323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767479375405411946192861 287804765777029479822323)
                  ·
                    rfl

theorem cell20_630560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_630560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630560 prefixEnd_630560 := by exact prefixLift 630560
  have htrace : WordTrace (prefixWord ++ tailWord_630560) baseStart_630560 baseEnd_630560 := by
    simpa [prefixWord, tailWord_630560, baseEnd_630560] using wordTrace_append hprefix tailTrace_630560
  have hstable : (prefixWord ++ tailWord_630560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630560).length < 2 ^ (prefixWord ++ tailWord_630560).sum := by decide
  have hdescent : baseEnd_630560 < baseStart_630560 := by decide
  rcases family_descends (prefixWord ++ tailWord_630560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630584 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_630584 : Nat := 118140960795 + 630584 * 2 ^ 59
def prefixEnd_630584 : Nat := 4983230072969 + 3 ^ 40 * 630584 * 2
def baseEnd_630584 : Nat := 287815720030992063022225

theorem tailTrace_630584 : CollatzResearch.WordTrace tailWord_630584 prefixEnd_630584 287815720030992063022225 := by
  unfold tailWord_630584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11499643973754669009129403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15332858631672892012172537 11499643973754669009129403)
  ·
    refine ⟨17249465960632003513694105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11499643973754669009129403 17249465960632003513694105)
    ·
      refine ⟨12937099470474002635270579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17249465960632003513694105 12937099470474002635270579)
      ·
        refine ⟨19405649205711003952905869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12937099470474002635270579 19405649205711003952905869)
        ·
          refine ⟨7277118452141626482339701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19405649205711003952905869 7277118452141626482339701)
          ·
            refine ⟨682229854888277482719347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7277118452141626482339701 682229854888277482719347)
            ·
              refine ⟨1023344782332416224079021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682229854888277482719347 1023344782332416224079021)
              ·
                refine ⟨383754293374656084029633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023344782332416224079021 383754293374656084029633)
                ·
                  refine ⟨287815720030992063022225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383754293374656084029633 287815720030992063022225)
                  ·
                    rfl

theorem cell20_630584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_630584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630584 prefixEnd_630584 := by exact prefixLift 630584
  have htrace : WordTrace (prefixWord ++ tailWord_630584) baseStart_630584 baseEnd_630584 := by
    simpa [prefixWord, tailWord_630584, baseEnd_630584] using wordTrace_append hprefix tailTrace_630584
  have hstable : (prefixWord ++ tailWord_630584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630584).length < 2 ^ (prefixWord ++ tailWord_630584).sum := by decide
  have hdescent : baseEnd_630584 < baseStart_630584 := by decide
  rcases family_descends (prefixWord ++ tailWord_630584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630595 : List Nat := [1, 1, 1, 3, 1, 7, 6]
def baseStart_630595 : Nat := 118140960795 + 630595 * 2 ^ 59
def prefixEnd_630595 : Nat := 4983230072969 + 3 ^ 40 * 630595 * 2
def baseEnd_630595 : Nat := 31980082303413879295057

theorem tailTrace_630595 : CollatzResearch.WordTrace tailWord_630595 prefixEnd_630595 31980082303413879295057 := by
  unfold tailWord_630595
  simp only [CollatzResearch.WordTrace]
  refine ⟨22999689150469486896909239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15333126100312991264606159 22999689150469486896909239)
  ·
    refine ⟨34499533725704230345363859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22999689150469486896909239 34499533725704230345363859)
    ·
      refine ⟨51749300588556345518045789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34499533725704230345363859 51749300588556345518045789)
      ·
        refine ⟨19405987720708629569267171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51749300588556345518045789 19405987720708629569267171)
        ·
          refine ⟨29108981581062944353900757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19405987720708629569267171 29108981581062944353900757)
          ·
            refine ⟨682241755806162758294549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29108981581062944353900757 682241755806162758294549)
            ·
              refine ⟨31980082303413879295057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 682241755806162758294549 31980082303413879295057)
              ·
                rfl

theorem cell20_630595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_630595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630595 prefixEnd_630595 := by exact prefixLift 630595
  have htrace : WordTrace (prefixWord ++ tailWord_630595) baseStart_630595 baseEnd_630595 := by
    simpa [prefixWord, tailWord_630595, baseEnd_630595] using wordTrace_append hprefix tailTrace_630595
  have hstable : (prefixWord ++ tailWord_630595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630595).length < 2 ^ (prefixWord ++ tailWord_630595).sum := by decide
  have hdescent : baseEnd_630595 < baseStart_630595 := by decide
  rcases family_descends (prefixWord ++ tailWord_630595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630602 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_630602 : Nat := 118140960795 + 630602 * 2 ^ 59
def prefixEnd_630602 : Nat := 4983230072969 + 3 ^ 40 * 630602 * 2
def baseEnd_630602 : Nat := 287823935721464000422151

theorem tailTrace_630602 : CollatzResearch.WordTrace tailWord_630602 prefixEnd_630602 287823935721464000422151 := by
  unfold tailWord_630602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5749986115361031773103515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15333296307629418061609373 5749986115361031773103515)
  ·
    refine ⟨8624979173041547659655273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5749986115361031773103515 8624979173041547659655273)
    ·
      refine ⟨6468734379781160744741455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8624979173041547659655273 6468734379781160744741455)
      ·
        refine ⟨9703101569671741117112183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6468734379781160744741455 9703101569671741117112183)
        ·
          refine ⟨14554652354507611675668275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9703101569671741117112183 14554652354507611675668275)
          ·
            refine ⟨21831978531761417513502413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14554652354507611675668275 21831978531761417513502413)
            ·
              refine ⟨8186991949410531567563405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21831978531761417513502413 8186991949410531567563405)
              ·
                refine ⟨3070121981028949337836277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8186991949410531567563405 3070121981028949337836277)
                ·
                  refine ⟨287823935721464000422151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070121981028949337836277 287823935721464000422151)
                  ·
                    rfl

theorem cell20_630602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_630602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630602 prefixEnd_630602 := by exact prefixLift 630602
  have htrace : WordTrace (prefixWord ++ tailWord_630602) baseStart_630602 baseEnd_630602 := by
    simpa [prefixWord, tailWord_630602, baseEnd_630602] using wordTrace_append hprefix tailTrace_630602
  have hstable : (prefixWord ++ tailWord_630602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630602).length < 2 ^ (prefixWord ++ tailWord_630602).sum := by decide
  have hdescent : baseEnd_630602 < baseStart_630602 := by decide
  rcases family_descends (prefixWord ++ tailWord_630602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630612 : List Nat := [2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_630612 : Nat := 118140960795 + 630612 * 2 ^ 59
def prefixEnd_630612 : Nat := 4983230072969 + 3 ^ 40 * 630612 * 2
def baseEnd_630612 : Nat := 95942833331316136696259

theorem tailTrace_630612 : CollatzResearch.WordTrace tailWord_630612 prefixEnd_630612 95942833331316136696259 := by
  unfold tailWord_630612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11500154595703949400139045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15333539460938599200185393 11500154595703949400139045)
  ·
    refine ⟨2156278986694490512526071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11500154595703949400139045 2156278986694490512526071)
    ·
      refine ⟨3234418480041735768789107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156278986694490512526071 3234418480041735768789107)
      ·
        refine ⟨4851627720062603653183661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234418480041735768789107 4851627720062603653183661)
        ·
          refine ⟨1819360395023476369943873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4851627720062603653183661 1819360395023476369943873)
          ·
            refine ⟨1364520296267607277457905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819360395023476369943873 1364520296267607277457905)
            ·
              refine ⟨1023390222200705458093429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364520296267607277457905 1023390222200705458093429)
              ·
                refine ⟨95942833331316136696259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023390222200705458093429 95942833331316136696259)
                ·
                  rfl

theorem cell20_630612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_630612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630612 prefixEnd_630612 := by exact prefixLift 630612
  have htrace : WordTrace (prefixWord ++ tailWord_630612) baseStart_630612 baseEnd_630612 := by
    simpa [prefixWord, tailWord_630612, baseEnd_630612] using wordTrace_append hprefix tailTrace_630612
  have hstable : (prefixWord ++ tailWord_630612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630612).length < 2 ^ (prefixWord ++ tailWord_630612).sum := by decide
  have hdescent : baseEnd_630612 < baseStart_630612 := by decide
  rcases family_descends (prefixWord ++ tailWord_630612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630615 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 3]
def baseStart_630615 : Nat := 118140960795 + 630615 * 2 ^ 59
def prefixEnd_630615 : Nat := 4983230072969 + 3 ^ 40 * 630615 * 2
def baseEnd_630615 : Nat := 287829869275693732988765

theorem tailTrace_630615 : CollatzResearch.WordTrace tailWord_630615 prefixEnd_630615 287829869275693732988765 := by
  unfold tailWord_630615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23000418610397030312637299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15333612406931353541758199 23000418610397030312637299)
  ·
    refine ⟨34500627915595545468955949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23000418610397030312637299 34500627915595545468955949)
    ·
      refine ⟨12937735468348329550858481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34500627915595545468955949 12937735468348329550858481)
      ·
        refine ⟨9703301601261247163143861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12937735468348329550858481 9703301601261247163143861)
        ·
          refine ⟨909684525118241921544737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9703301601261247163143861 909684525118241921544737)
          ·
            refine ⟨682263393838681441158553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909684525118241921544737 682263393838681441158553)
            ·
              refine ⟨511697545379011080868915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682263393838681441158553 511697545379011080868915)
              ·
                refine ⟨767546318068516621303373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511697545379011080868915 767546318068516621303373)
                ·
                  refine ⟨287829869275693732988765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767546318068516621303373 287829869275693732988765)
                  ·
                    rfl

theorem cell20_630615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_630615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630615 prefixEnd_630615 := by exact prefixLift 630615
  have htrace : WordTrace (prefixWord ++ tailWord_630615) baseStart_630615 baseEnd_630615 := by
    simpa [prefixWord, tailWord_630615, baseEnd_630615] using wordTrace_append hprefix tailTrace_630615
  have hstable : (prefixWord ++ tailWord_630615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630615).length < 2 ^ (prefixWord ++ tailWord_630615).sum := by decide
  have hdescent : baseEnd_630615 < baseStart_630615 := by decide
  rcases family_descends (prefixWord ++ tailWord_630615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630660 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_630660 : Nat := 118140960795 + 630660 * 2 ^ 59
def prefixEnd_630660 : Nat := 4983230072969 + 3 ^ 40 * 630660 * 2
def baseEnd_630660 : Nat := 287850408501873576488581

theorem tailTrace_630660 : CollatzResearch.WordTrace tailWord_630660 prefixEnd_630660 287850408501873576488581 := by
  unfold tailWord_630660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501029947617001499012717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15334706596822668665350289 11501029947617001499012717)
  ·
    refine ⟨4312886230356375562129769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11501029947617001499012717 4312886230356375562129769)
    ·
      refine ⟨3234664672767281671597327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4312886230356375562129769 3234664672767281671597327)
      ·
        refine ⟨4851997009150922507395991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234664672767281671597327 4851997009150922507395991)
        ·
          refine ⟨7277995513726383761093987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851997009150922507395991 7277995513726383761093987)
          ·
            refine ⟨10916993270589575641640981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277995513726383761093987 10916993270589575641640981)
            ·
              refine ⟨511734059558886358201921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10916993270589575641640981 511734059558886358201921)
              ·
                refine ⟨383800544669164768651441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511734059558886358201921 383800544669164768651441)
                ·
                  refine ⟨287850408501873576488581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383800544669164768651441 287850408501873576488581)
                  ·
                    rfl

theorem cell20_630660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_630660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630660 prefixEnd_630660 := by exact prefixLift 630660
  have htrace : WordTrace (prefixWord ++ tailWord_630660) baseStart_630660 baseEnd_630660 := by
    simpa [prefixWord, tailWord_630660, baseEnd_630660] using wordTrace_append hprefix tailTrace_630660
  have hstable : (prefixWord ++ tailWord_630660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630660).length < 2 ^ (prefixWord ++ tailWord_630660).sum := by decide
  have hdescent : baseEnd_630660 < baseStart_630660 := by decide
  rcases family_descends (prefixWord ++ tailWord_630660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630674 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_630674 : Nat := 118140960795 + 630674 * 2 ^ 59
def prefixEnd_630674 : Nat := 4983230072969 + 3 ^ 40 * 630674 * 2
def baseEnd_630674 : Nat := 287856798483351750021857

theorem tailTrace_630674 : CollatzResearch.WordTrace tailWord_630674 prefixEnd_630674 287856798483351750021857 := by
  unfold tailWord_630674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750642629295820847258769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15335047011455522259356717 5750642629295820847258769)
  ·
    refine ⟨4312981971971865635444077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5750642629295820847258769 4312981971971865635444077)
    ·
      refine ⟨1617368239489449613291529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4312981971971865635444077 1617368239489449613291529)
      ·
        refine ⟨1213026179617087209968647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617368239489449613291529 1213026179617087209968647)
        ·
          refine ⟨1819539269425630814952971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213026179617087209968647 1819539269425630814952971)
          ·
            refine ⟨2729308904138446222429457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819539269425630814952971 2729308904138446222429457)
            ·
              refine ⟨2046981678103834666822093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729308904138446222429457 2046981678103834666822093)
              ·
                refine ⟨767618129288938000058285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046981678103834666822093 767618129288938000058285)
                ·
                  refine ⟨287856798483351750021857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767618129288938000058285 287856798483351750021857)
                  ·
                    rfl

theorem cell20_630674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_630674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630674 prefixEnd_630674 := by exact prefixLift 630674
  have htrace : WordTrace (prefixWord ++ tailWord_630674) baseStart_630674 baseEnd_630674 := by
    simpa [prefixWord, tailWord_630674, baseEnd_630674] using wordTrace_append hprefix tailTrace_630674
  have hstable : (prefixWord ++ tailWord_630674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630674).length < 2 ^ (prefixWord ++ tailWord_630674).sum := by decide
  have hdescent : baseEnd_630674 < baseStart_630674 := by decide
  rcases family_descends (prefixWord ++ tailWord_630674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630708 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_630708 : Nat := 118140960795 + 630708 * 2 ^ 59
def prefixEnd_630708 : Nat := 4983230072969 + 3 ^ 40 * 630708 * 2
def baseEnd_630708 : Nat := 287872317009798742888385

theorem tailTrace_630708 : CollatzResearch.WordTrace tailWord_630708 prefixEnd_630708 287872317009798742888385 := by
  unfold tailWord_630708
  simp only [CollatzResearch.WordTrace]
  refine ⟨11501905299530053597886389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15335873732706738130515185 11501905299530053597886389)
  ·
    refine ⟨1078303621830942524801849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11501905299530053597886389 1078303621830942524801849)
    ·
      refine ⟨808727716373206893601387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078303621830942524801849 808727716373206893601387)
      ·
        refine ⟨1213091574559810340402081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808727716373206893601387 1213091574559810340402081)
        ·
          refine ⟨909818680919857755301561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213091574559810340402081 909818680919857755301561)
          ·
            refine ⟨682364010689893316476171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909818680919857755301561 682364010689893316476171)
            ·
              refine ⟨1023546016034839974714257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682364010689893316476171 1023546016034839974714257)
              ·
                refine ⟨767659512026129981035693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023546016034839974714257 767659512026129981035693)
                ·
                  refine ⟨287872317009798742888385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767659512026129981035693 287872317009798742888385)
                  ·
                    rfl

theorem cell20_630708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_630708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630708 prefixEnd_630708 := by exact prefixLift 630708
  have htrace : WordTrace (prefixWord ++ tailWord_630708) baseStart_630708 baseEnd_630708 := by
    simpa [prefixWord, tailWord_630708, baseEnd_630708] using wordTrace_append hprefix tailTrace_630708
  have hstable : (prefixWord ++ tailWord_630708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630708).length < 2 ^ (prefixWord ++ tailWord_630708).sum := by decide
  have hdescent : baseEnd_630708 < baseStart_630708 := by decide
  rcases family_descends (prefixWord ++ tailWord_630708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630709 : List Nat := [1, 3, 3, 2, 1, 3, 7]
def baseStart_630709 : Nat := 118140960795 + 630709 * 2 ^ 59
def prefixEnd_630709 : Nat := 4983230072969 + 3 ^ 40 * 630709 * 2
def baseEnd_630709 : Nat := 31985863715227464872783

theorem tailTrace_630709 : CollatzResearch.WordTrace tailWord_630709 prefixEnd_630709 31985863715227464872783 := by
  unfold tailWord_630709
  simp only [CollatzResearch.WordTrace]
  refine ⟨23003847072056484366559181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15335898048037656244372787 23003847072056484366559181)
  ·
    refine ⟨8626442652021181637459693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23003847072056484366559181 8626442652021181637459693)
    ·
      refine ⟨3234915994507943114047385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8626442652021181637459693 3234915994507943114047385)
      ·
        refine ⟨2426186995880957335535539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3234915994507943114047385 2426186995880957335535539)
        ·
          refine ⟨3639280493821436003303309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426186995880957335535539 3639280493821436003303309)
          ·
            refine ⟨1364730185183038501238741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3639280493821436003303309 1364730185183038501238741)
            ·
              refine ⟨31985863715227464872783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1364730185183038501238741 31985863715227464872783)
              ·
                rfl

theorem cell20_630709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_630709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630709 prefixEnd_630709 := by exact prefixLift 630709
  have htrace : WordTrace (prefixWord ++ tailWord_630709) baseStart_630709 baseEnd_630709 := by
    simpa [prefixWord, tailWord_630709, baseEnd_630709] using wordTrace_append hprefix tailTrace_630709
  have hstable : (prefixWord ++ tailWord_630709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630709).length < 2 ^ (prefixWord ++ tailWord_630709).sum := by decide
  have hdescent : baseEnd_630709 < baseStart_630709 := by decide
  rcases family_descends (prefixWord ++ tailWord_630709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630740 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_630740 : Nat := 118140960795 + 630740 * 2 ^ 59
def prefixEnd_630740 : Nat := 4983230072969 + 3 ^ 40 * 630740 * 2
def baseEnd_630740 : Nat := 287886922681748853821587

theorem tailTrace_630740 : CollatzResearch.WordTrace tailWord_630740 prefixEnd_630740 287886922681748853821587 := by
  unfold tailWord_630740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502488867472088330468837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15336651823296117773958449 11502488867472088330468837)
  ·
    refine ⟨2156716662651016561962907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11502488867472088330468837 2156716662651016561962907)
    ·
      refine ⟨3235074993976524842944361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156716662651016561962907 3235074993976524842944361)
      ·
        refine ⟨2426306245482393632208271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3235074993976524842944361 2426306245482393632208271)
        ·
          refine ⟨3639459368223590448312407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426306245482393632208271 3639459368223590448312407)
          ·
            refine ⟨5459189052335385672468611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639459368223590448312407 5459189052335385672468611)
            ·
              refine ⟨8188783578503078508702917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459189052335385672468611 8188783578503078508702917)
              ·
                refine ⟨1535396920969327220381797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8188783578503078508702917 1535396920969327220381797)
                ·
                  refine ⟨287886922681748853821587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535396920969327220381797 287886922681748853821587)
                  ·
                    rfl

theorem cell20_630740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_630740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630740 prefixEnd_630740 := by exact prefixLift 630740
  have htrace : WordTrace (prefixWord ++ tailWord_630740) baseStart_630740 baseEnd_630740 := by
    simpa [prefixWord, tailWord_630740, baseEnd_630740] using wordTrace_append hprefix tailTrace_630740
  have hstable : (prefixWord ++ tailWord_630740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630740).length < 2 ^ (prefixWord ++ tailWord_630740).sum := by decide
  have hdescent : baseEnd_630740 < baseStart_630740 := by decide
  rcases family_descends (prefixWord ++ tailWord_630740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630768 : List Nat := [2, 1, 1, 1, 3, 2, 10]
def baseStart_630768 : Nat := 118140960795 + 630768 * 2 ^ 59
def prefixEnd_630768 : Nat := 4983230072969 + 3 ^ 40 * 630768 * 2
def baseEnd_630768 : Nat := 31988855849411688987571

theorem tailTrace_630768 : CollatzResearch.WordTrace tailWord_630768 prefixEnd_630768 31988855849411688987571 := by
  unfold tailWord_630768
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502999489421368721478479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15337332652561824961971305 11502999489421368721478479)
  ·
    refine ⟨17254499234132053082217719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11502999489421368721478479 17254499234132053082217719)
    ·
      refine ⟨25881748851198079623326579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17254499234132053082217719 25881748851198079623326579)
      ·
        refine ⟨38822623276797119434989869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25881748851198079623326579 38822623276797119434989869)
        ·
          refine ⟨14558483728798919788121201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38822623276797119434989869 14558483728798919788121201)
          ·
            refine ⟨10918862796599189841090901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14558483728798919788121201 10918862796599189841090901)
            ·
              refine ⟨31988855849411688987571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10918862796599189841090901 31988855849411688987571)
              ·
                rfl

theorem cell20_630768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_630768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630768 prefixEnd_630768 := by exact prefixLift 630768
  have htrace : WordTrace (prefixWord ++ tailWord_630768) baseStart_630768 baseEnd_630768 := by
    simpa [prefixWord, tailWord_630768, baseEnd_630768] using wordTrace_append hprefix tailTrace_630768
  have hstable : (prefixWord ++ tailWord_630768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630768).length < 2 ^ (prefixWord ++ tailWord_630768).sum := by decide
  have hdescent : baseEnd_630768 < baseStart_630768 := by decide
  rcases family_descends (prefixWord ++ tailWord_630768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630774 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_630774 : Nat := 118140960795 + 630774 * 2 ^ 59
def prefixEnd_630774 : Nat := 4983230072969 + 3 ^ 40 * 630774 * 2
def baseEnd_630774 : Nat := 287902441208195846688115

theorem tailTrace_630774 : CollatzResearch.WordTrace tailWord_630774 prefixEnd_630774 287902441208195846688115 := by
  unfold tailWord_630774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437888613551312529229711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15337478544547333645116917 1437888613551312529229711)
  ·
    refine ⟨2156832920326968793844567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437888613551312529229711 2156832920326968793844567)
    ·
      refine ⟨3235249380490453190766851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156832920326968793844567 3235249380490453190766851)
      ·
        refine ⟨4852874070735679786150277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235249380490453190766851 4852874070735679786150277)
        ·
          refine ⟨909913888262939959903177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4852874070735679786150277 909913888262939959903177)
          ·
            refine ⟨682435416197204969927383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909913888262939959903177 682435416197204969927383)
            ·
              refine ⟨1023653124295807454891075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682435416197204969927383 1023653124295807454891075)
              ·
                refine ⟨1535479686443711182336613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023653124295807454891075 1535479686443711182336613)
                ·
                  refine ⟨287902441208195846688115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535479686443711182336613 287902441208195846688115)
                  ·
                    rfl

theorem cell20_630774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_630774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630774 prefixEnd_630774 := by exact prefixLift 630774
  have htrace : WordTrace (prefixWord ++ tailWord_630774) baseStart_630774 baseEnd_630774 := by
    simpa [prefixWord, tailWord_630774, baseEnd_630774] using wordTrace_append hprefix tailTrace_630774
  have hstable : (prefixWord ++ tailWord_630774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630774).length < 2 ^ (prefixWord ++ tailWord_630774).sum := by decide
  have hdescent : baseEnd_630774 < baseStart_630774 := by decide
  rcases family_descends (prefixWord ++ tailWord_630774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630785 : List Nat := [1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_630785 : Nat := 118140960795 + 630785 * 2 ^ 59
def prefixEnd_630785 : Nat := 4983230072969 + 3 ^ 40 * 630785 * 2
def baseEnd_630785 : Nat := 95969153969309565773801

theorem tailTrace_630785 : CollatzResearch.WordTrace tailWord_630785 prefixEnd_630785 95969153969309565773801 := by
  unfold tailWord_630785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23006619019781149346325809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15337746013187432897550539 23006619019781149346325809)
  ·
    refine ⟨17254964264835862009744357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23006619019781149346325809 17254964264835862009744357)
    ·
      refine ⟨3235305799656724126827067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17254964264835862009744357 3235305799656724126827067)
      ·
        refine ⟨4852958699485086190240601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235305799656724126827067 4852958699485086190240601)
        ·
          refine ⟨3639719024613814642680451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4852958699485086190240601 3639719024613814642680451)
          ·
            refine ⟨5459578536920721964020677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639719024613814642680451 5459578536920721964020677)
            ·
              refine ⟨1023670975672635368253877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5459578536920721964020677 1023670975672635368253877)
              ·
                refine ⟨95969153969309565773801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023670975672635368253877 95969153969309565773801)
                ·
                  rfl

theorem cell20_630785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_630785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630785 prefixEnd_630785 := by exact prefixLift 630785
  have htrace : WordTrace (prefixWord ++ tailWord_630785) baseStart_630785 baseEnd_630785 := by
    simpa [prefixWord, tailWord_630785, baseEnd_630785] using wordTrace_append hprefix tailTrace_630785
  have hstable : (prefixWord ++ tailWord_630785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630785).length < 2 ^ (prefixWord ++ tailWord_630785).sum := by decide
  have hdescent : baseEnd_630785 < baseStart_630785 := by decide
  rcases family_descends (prefixWord ++ tailWord_630785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630823 : List Nat := [1, 1, 7, 1, 10]
def baseStart_630823 : Nat := 118140960795 + 630823 * 2 ^ 59
def prefixEnd_630823 : Nat := 4983230072969 + 3 ^ 40 * 630823 * 2
def baseEnd_630823 : Nat := 3554627236337894494501

theorem tailTrace_630823 : CollatzResearch.WordTrace tailWord_630823 prefixEnd_630823 3554627236337894494501 := by
  unfold tailWord_630823
  simp only [CollatzResearch.WordTrace]
  refine ⟨23008004993643481836209123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15338669995762321224139415 23008004993643481836209123)
  ·
    refine ⟨34512007490465222754313685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23008004993643481836209123 34512007490465222754313685)
    ·
      refine ⟨808875175557778658304227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34512007490465222754313685 808875175557778658304227)
      ·
        refine ⟨1213312763336667987456341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808875175557778658304227 1213312763336667987456341)
        ·
          refine ⟨3554627236337894494501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1213312763336667987456341 3554627236337894494501)
          ·
            rfl

theorem cell20_630823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 10].length) (baseStart_630823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630823 prefixEnd_630823 := by exact prefixLift 630823
  have htrace : WordTrace (prefixWord ++ tailWord_630823) baseStart_630823 baseEnd_630823 := by
    simpa [prefixWord, tailWord_630823, baseEnd_630823] using wordTrace_append hprefix tailTrace_630823
  have hstable : (prefixWord ++ tailWord_630823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630823).length < 2 ^ (prefixWord ++ tailWord_630823).sum := by decide
  have hdescent : baseEnd_630823 < baseStart_630823 := by decide
  rcases family_descends (prefixWord ++ tailWord_630823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630826 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_630826 : Nat := 118140960795 + 630826 * 2 ^ 59
def prefixEnd_630826 : Nat := 4983230072969 + 3 ^ 40 * 630826 * 2
def baseEnd_630826 : Nat := 287926175425114776954569

theorem tailTrace_630826 : CollatzResearch.WordTrace tailWord_630826 prefixEnd_630826 287926175425114776954569 := by
  unfold tailWord_630826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752028603158153337142083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15338742941755075565712221 5752028603158153337142083)
  ·
    refine ⟨8628042904737230005713125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5752028603158153337142083 8628042904737230005713125)
    ·
      refine ⟨1617758044638230626071211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8628042904737230005713125 1617758044638230626071211)
      ·
        refine ⟨2426637066957345939106817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617758044638230626071211 2426637066957345939106817)
        ·
          refine ⟨1819977800218009454330113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426637066957345939106817 1819977800218009454330113)
          ·
            refine ⟨1364983350163507090747585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819977800218009454330113 1364983350163507090747585)
            ·
              refine ⟨1023737512622630318060689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364983350163507090747585 1023737512622630318060689)
              ·
                refine ⟨767803134466972738545517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023737512622630318060689 767803134466972738545517)
                ·
                  refine ⟨287926175425114776954569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767803134466972738545517 287926175425114776954569)
                  ·
                    rfl

theorem cell20_630826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_630826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630826 prefixEnd_630826 := by exact prefixLift 630826
  have htrace : WordTrace (prefixWord ++ tailWord_630826) baseStart_630826 baseEnd_630826 := by
    simpa [prefixWord, tailWord_630826, baseEnd_630826] using wordTrace_append hprefix tailTrace_630826
  have hstable : (prefixWord ++ tailWord_630826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630826).length < 2 ^ (prefixWord ++ tailWord_630826).sum := by decide
  have hdescent : baseEnd_630826 < baseStart_630826 := by decide
  rcases family_descends (prefixWord ++ tailWord_630826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630833 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 2]
def baseStart_630833 : Nat := 118140960795 + 630833 * 2 ^ 59
def prefixEnd_630833 : Nat := 4983230072969 + 3 ^ 40 * 630833 * 2
def baseEnd_630833 : Nat := 287929370415853863721207

theorem tailTrace_630833 : CollatzResearch.WordTrace tailWord_630833 prefixEnd_630833 287929370415853863721207 := by
  unfold tailWord_630833
  simp only [CollatzResearch.WordTrace]
  refine ⟨23008369723607253544073153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15338913149071502362715435 23008369723607253544073153)
  ·
    refine ⟨17256277292705440158054865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23008369723607253544073153 17256277292705440158054865)
    ·
      refine ⟨12942207969529080118541149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17256277292705440158054865 12942207969529080118541149)
      ·
        refine ⟨4853327988573405044452931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12942207969529080118541149 4853327988573405044452931)
        ·
          refine ⟨7279991982860107566679397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853327988573405044452931 7279991982860107566679397)
          ·
            refine ⟨1364998496786270168752387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7279991982860107566679397 1364998496786270168752387)
            ·
              refine ⟨2047497745179405253128581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364998496786270168752387 2047497745179405253128581)
              ·
                refine ⟨383905827221138484961609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2047497745179405253128581 383905827221138484961609)
                ·
                  refine ⟨287929370415853863721207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383905827221138484961609 287929370415853863721207)
                  ·
                    rfl

theorem cell20_630833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_630833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630833 prefixEnd_630833 := by exact prefixLift 630833
  have htrace : WordTrace (prefixWord ++ tailWord_630833) baseStart_630833 baseEnd_630833 := by
    simpa [prefixWord, tailWord_630833, baseEnd_630833] using wordTrace_append hprefix tailTrace_630833
  have hstable : (prefixWord ++ tailWord_630833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630833).length < 2 ^ (prefixWord ++ tailWord_630833).sum := by decide
  have hdescent : baseEnd_630833 < baseStart_630833 := by decide
  rcases family_descends (prefixWord ++ tailWord_630833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630836 : List Nat := [2, 5, 1, 2, 3, 1, 1, 5]
def baseStart_630836 : Nat := 118140960795 + 630836 * 2 ^ 59
def prefixEnd_630836 : Nat := 4983230072969 + 3 ^ 40 * 630836 * 2
def baseEnd_630836 : Nat := 95976913232533062207065

theorem tailTrace_630836 : CollatzResearch.WordTrace tailWord_630836 prefixEnd_630836 95976913232533062207065 := by
  unfold tailWord_630836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504239571298192528216181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15338986095064256704288241 11504239571298192528216181)
  ·
    refine ⟨1078522459809205549520267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11504239571298192528216181 1078522459809205549520267)
    ·
      refine ⟨1617783689713808324280401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078522459809205549520267 1617783689713808324280401)
      ·
        refine ⟨1213337767285356243210301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617783689713808324280401 1213337767285356243210301)
        ·
          refine ⟨455001662732008591203863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1213337767285356243210301 455001662732008591203863)
          ·
            refine ⟨682502494098012886805795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455001662732008591203863 682502494098012886805795)
            ·
              refine ⟨1023753741147019330208693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682502494098012886805795 1023753741147019330208693)
              ·
                refine ⟨95976913232533062207065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023753741147019330208693 95976913232533062207065)
                ·
                  rfl

theorem cell20_630836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_630836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630836 prefixEnd_630836 := by exact prefixLift 630836
  have htrace : WordTrace (prefixWord ++ tailWord_630836) baseStart_630836 baseEnd_630836 := by
    simpa [prefixWord, tailWord_630836, baseEnd_630836] using wordTrace_append hprefix tailTrace_630836
  have hstable : (prefixWord ++ tailWord_630836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630836).length < 2 ^ (prefixWord ++ tailWord_630836).sum := by decide
  have hdescent : baseEnd_630836 < baseStart_630836 := by decide
  rcases family_descends (prefixWord ++ tailWord_630836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630840 : List Nat := [2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_630840 : Nat := 118140960795 + 630840 * 2 ^ 59
def prefixEnd_630840 : Nat := 4983230072969 + 3 ^ 40 * 630840 * 2
def baseEnd_630840 : Nat := 95977521802197650162615

theorem tailTrace_630840 : CollatzResearch.WordTrace tailWord_630840 prefixEnd_630840 95977521802197650162615 := by
  unfold tailWord_630840
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504312517290946869788987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15339083356387929159718649 11504312517290946869788987)
  ·
    refine ⟨17256468775936420304683481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504312517290946869788987 17256468775936420304683481)
    ·
      refine ⟨12942351581952315228512611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17256468775936420304683481 12942351581952315228512611)
      ·
        refine ⟨19413527372928472842768917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12942351581952315228512611 19413527372928472842768917)
        ·
          refine ⟨910009095606022164504793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19413527372928472842768917 910009095606022164504793)
          ·
            refine ⟨682506821704516623378595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910009095606022164504793 682506821704516623378595)
            ·
              refine ⟨1023760232556774935067893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682506821704516623378595 1023760232556774935067893)
              ·
                refine ⟨95977521802197650162615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023760232556774935067893 95977521802197650162615)
                ·
                  rfl

theorem cell20_630840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_630840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630840 prefixEnd_630840 := by exact prefixLift 630840
  have htrace : WordTrace (prefixWord ++ tailWord_630840) baseStart_630840 baseEnd_630840 := by
    simpa [prefixWord, tailWord_630840, baseEnd_630840] using wordTrace_append hprefix tailTrace_630840
  have hstable : (prefixWord ++ tailWord_630840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630840).length < 2 ^ (prefixWord ++ tailWord_630840).sum := by decide
  have hdescent : baseEnd_630840 < baseStart_630840 := by decide
  rcases family_descends (prefixWord ++ tailWord_630840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630868 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_630868 : Nat := 118140960795 + 630868 * 2 ^ 59
def prefixEnd_630868 : Nat := 4983230072969 + 3 ^ 40 * 630868 * 2
def baseEnd_630868 : Nat := 287945345369549297554397

theorem tailTrace_630868 : CollatzResearch.WordTrace tailWord_630868 prefixEnd_630868 287945345369549297554397 := by
  unfold tailWord_630868
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504823139240227260798629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15339764185653636347731505 11504823139240227260798629)
  ·
    refine ⟨2157154338607542611399743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11504823139240227260798629 2157154338607542611399743)
    ·
      refine ⟨3235731507911313917099615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157154338607542611399743 3235731507911313917099615)
      ·
        refine ⟨4853597261866970875649423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235731507911313917099615 4853597261866970875649423)
        ·
          refine ⟨7280395892800456313474135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853597261866970875649423 7280395892800456313474135)
          ·
            refine ⟨10920593839200684470211203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280395892800456313474135 10920593839200684470211203)
            ·
              refine ⟨16380890758801026705316805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10920593839200684470211203 16380890758801026705316805)
              ·
                refine ⟨3071417017275192507246901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16380890758801026705316805 3071417017275192507246901)
                ·
                  refine ⟨287945345369549297554397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3071417017275192507246901 287945345369549297554397)
                  ·
                    rfl

theorem cell20_630868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_630868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630868 prefixEnd_630868 := by exact prefixLift 630868
  have htrace : WordTrace (prefixWord ++ tailWord_630868) baseStart_630868 baseEnd_630868 := by
    simpa [prefixWord, tailWord_630868, baseEnd_630868] using wordTrace_append hprefix tailTrace_630868
  have hstable : (prefixWord ++ tailWord_630868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630868).length < 2 ^ (prefixWord ++ tailWord_630868).sum := by decide
  have hdescent : baseEnd_630868 < baseStart_630868 := by decide
  rcases family_descends (prefixWord ++ tailWord_630868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630885 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_630885 : Nat := 118140960795 + 630885 * 2 ^ 59
def prefixEnd_630885 : Nat := 4983230072969 + 3 ^ 40 * 630885 * 2
def baseEnd_630885 : Nat := 287953104632772793987661

theorem tailTrace_630885 : CollatzResearch.WordTrace tailWord_630885 prefixEnd_630885 287953104632772793987661 := by
  unfold tailWord_630885
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010266319418866424966109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15340177546279244283310739 23010266319418866424966109)
  ·
    refine ⟨8628849869782074909362291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23010266319418866424966109 8628849869782074909362291)
    ·
      refine ⟨12943274804673112364043437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8628849869782074909362291 12943274804673112364043437)
      ·
        refine ⟨4853728051752417136516289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12943274804673112364043437 4853728051752417136516289)
        ·
          refine ⟨3640296038814312852387217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853728051752417136516289 3640296038814312852387217)
          ·
            refine ⟨2730222029110734639290413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3640296038814312852387217 2730222029110734639290413)
            ·
              refine ⟨1023833260916525489733905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2730222029110734639290413 1023833260916525489733905)
              ·
                refine ⟨767874945687394117300429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023833260916525489733905 767874945687394117300429)
                ·
                  refine ⟨287953104632772793987661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767874945687394117300429 287953104632772793987661)
                  ·
                    rfl

theorem cell20_630885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_630885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630885 prefixEnd_630885 := by exact prefixLift 630885
  have htrace : WordTrace (prefixWord ++ tailWord_630885) baseStart_630885 baseEnd_630885 := by
    simpa [prefixWord, tailWord_630885, baseEnd_630885] using wordTrace_append hprefix tailTrace_630885
  have hstable : (prefixWord ++ tailWord_630885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630885).length < 2 ^ (prefixWord ++ tailWord_630885).sum := by decide
  have hdescent : baseEnd_630885 < baseStart_630885 := by decide
  rcases family_descends (prefixWord ++ tailWord_630885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630892 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_630892 : Nat := 118140960795 + 630892 * 2 ^ 59
def prefixEnd_630892 : Nat := 4983230072969 + 3 ^ 40 * 630892 * 2
def baseEnd_630892 : Nat := 287956299623511880754299

theorem tailTrace_630892 : CollatzResearch.WordTrace tailWord_630892 prefixEnd_630892 287956299623511880754299 := by
  unfold tailWord_630892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11505260815196753310235465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15340347753595671080313953 11505260815196753310235465)
  ·
    refine ⟨8628945611397564982676599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11505260815196753310235465 8628945611397564982676599)
    ·
      refine ⟨12943418417096347474014899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8628945611397564982676599 12943418417096347474014899)
      ·
        refine ⟨19415127625644521211022349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12943418417096347474014899 19415127625644521211022349)
        ·
          refine ⟨7280672859616695454133381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19415127625644521211022349 7280672859616695454133381)
          ·
            refine ⟨1365126161178130397650009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7280672859616695454133381 1365126161178130397650009)
            ·
              refine ⟨1023844620883597798237507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365126161178130397650009 1023844620883597798237507)
              ·
                refine ⟨1535766931325396697356261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023844620883597798237507 1535766931325396697356261)
                ·
                  refine ⟨287956299623511880754299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1535766931325396697356261 287956299623511880754299)
                  ·
                    rfl

theorem cell20_630892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_630892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630892 prefixEnd_630892 := by exact prefixLift 630892
  have htrace : WordTrace (prefixWord ++ tailWord_630892) baseStart_630892 baseEnd_630892 := by
    simpa [prefixWord, tailWord_630892, baseEnd_630892] using wordTrace_append hprefix tailTrace_630892
  have hstable : (prefixWord ++ tailWord_630892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630892).length < 2 ^ (prefixWord ++ tailWord_630892).sum := by decide
  have hdescent : baseEnd_630892 < baseStart_630892 := by decide
  rcases family_descends (prefixWord ++ tailWord_630892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630944 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_630944 : Nat := 118140960795 + 630944 * 2 ^ 59
def prefixEnd_630944 : Nat := 4983230072969 + 3 ^ 40 * 630944 * 2
def baseEnd_630944 : Nat := 287980033840430811020753

theorem tailTrace_630944 : CollatzResearch.WordTrace tailWord_630944 prefixEnd_630944 287980033840430811020753 := by
  unfold tailWord_630944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506209113102559750681943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15341612150803413000909257 11506209113102559750681943)
  ·
    refine ⟨17259313669653839626022915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11506209113102559750681943 17259313669653839626022915)
    ·
      refine ⟨25888970504480759439034373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17259313669653839626022915 25888970504480759439034373)
      ·
        refine ⟨4854181969590142394818945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25888970504480759439034373 4854181969590142394818945)
        ·
          refine ⟨3640636477192606796114209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4854181969590142394818945 3640636477192606796114209)
          ·
            refine ⟨2730477357894455097085657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3640636477192606796114209 2730477357894455097085657)
            ·
              refine ⟨2047858018420841322814243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2730477357894455097085657 2047858018420841322814243)
              ·
                refine ⟨3071787027631261984221365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047858018420841322814243 3071787027631261984221365)
                ·
                  refine ⟨287980033840430811020753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3071787027631261984221365 287980033840430811020753)
                  ·
                    rfl

theorem cell20_630944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_630944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630944 prefixEnd_630944 := by exact prefixLift 630944
  have htrace : WordTrace (prefixWord ++ tailWord_630944) baseStart_630944 baseEnd_630944 := by
    simpa [prefixWord, tailWord_630944, baseEnd_630944] using wordTrace_append hprefix tailTrace_630944
  have hstable : (prefixWord ++ tailWord_630944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630944).length < 2 ^ (prefixWord ++ tailWord_630944).sum := by decide
  have hdescent : baseEnd_630944 < baseStart_630944 := by decide
  rcases family_descends (prefixWord ++ tailWord_630944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630957 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 3]
def baseStart_630957 : Nat := 118140960795 + 630957 * 2 ^ 59
def prefixEnd_630957 : Nat := 4983230072969 + 3 ^ 40 * 630957 * 2
def baseEnd_630957 : Nat := 287985967394660543587367

theorem tailTrace_630957 : CollatzResearch.WordTrace tailWord_630957 prefixEnd_630957 287985967394660543587367 := by
  unfold tailWord_630957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23012892375158022721587125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15341928250105348481058083 23012892375158022721587125)
  ·
    refine ⟨2157458660171064630148793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23012892375158022721587125 2157458660171064630148793)
    ·
      refine ⟨1618093995128298472611595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2157458660171064630148793 1618093995128298472611595)
      ·
        refine ⟨2427140992692447708917393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618093995128298472611595 2427140992692447708917393)
        ·
          refine ⟨1820355744519335781688045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427140992692447708917393 1820355744519335781688045)
          ·
            refine ⟨682633404194750918133017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1820355744519335781688045 682633404194750918133017)
            ·
              refine ⟨511975053146063188599763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682633404194750918133017 511975053146063188599763)
              ·
                refine ⟨767962579719094782899645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511975053146063188599763 767962579719094782899645)
                ·
                  refine ⟨287985967394660543587367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767962579719094782899645 287985967394660543587367)
                  ·
                    rfl

theorem cell20_630957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_630957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630957 prefixEnd_630957 := by exact prefixLift 630957
  have htrace : WordTrace (prefixWord ++ tailWord_630957) baseStart_630957 baseEnd_630957 := by
    simpa [prefixWord, tailWord_630957, baseEnd_630957] using wordTrace_append hprefix tailTrace_630957
  have hstable : (prefixWord ++ tailWord_630957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630957).length < 2 ^ (prefixWord ++ tailWord_630957).sum := by decide
  have hdescent : baseEnd_630957 < baseStart_630957 := by decide
  rcases family_descends (prefixWord ++ tailWord_630957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630996 : List Nat := [2, 4, 1, 13]
def baseStart_630996 : Nat := 118140960795 + 630996 * 2 ^ 59
def prefixEnd_630996 : Nat := 4983230072969 + 3 ^ 40 * 630996 * 2
def baseEnd_630996 : Nat := 1185200691594031857149

theorem tailTrace_630996 : CollatzResearch.WordTrace tailWord_630996 prefixEnd_630996 1185200691594031857149 := by
  unfold tailWord_630996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11507157411008366191128421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15342876548011154921504561 11507157411008366191128421)
  ·
    refine ⟨2157592014564068660836579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11507157411008366191128421 2157592014564068660836579)
    ·
      refine ⟨3236388021846102991254869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157592014564068660836579 3236388021846102991254869)
      ·
        refine ⟨1185200691594031857149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3236388021846102991254869 1185200691594031857149)
        ·
          rfl

theorem cell20_630996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 13].length) (baseStart_630996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630996 prefixEnd_630996 := by exact prefixLift 630996
  have htrace : WordTrace (prefixWord ++ tailWord_630996) baseStart_630996 baseEnd_630996 := by
    simpa [prefixWord, tailWord_630996, baseEnd_630996] using wordTrace_append hprefix tailTrace_630996
  have hstable : (prefixWord ++ tailWord_630996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630996).length < 2 ^ (prefixWord ++ tailWord_630996).sum := by decide
  have hdescent : baseEnd_630996 < baseStart_630996 := by decide
  rcases family_descends (prefixWord ++ tailWord_630996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630998 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_630998 : Nat := 118140960795 + 630998 * 2 ^ 59
def prefixEnd_630998 : Nat := 4983230072969 + 3 ^ 40 * 630998 * 2
def baseEnd_630998 : Nat := 288004680911846623220533

theorem tailTrace_630998 : CollatzResearch.WordTrace tailWord_630998 prefixEnd_630998 288004680911846623220533 := by
  unfold tailWord_630998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438399235500592920239353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15342925178672991149219765 1438399235500592920239353)
  ·
    refine ⟨1078799426625444690179515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1438399235500592920239353 1078799426625444690179515)
    ·
      refine ⟨1618199139938167035269273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078799426625444690179515 1618199139938167035269273)
      ·
        refine ⟨1213649354953625276451955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618199139938167035269273 1213649354953625276451955)
        ·
          refine ⟨1820474032430437914677933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213649354953625276451955 1820474032430437914677933)
          ·
            refine ⟨682677762161414218004225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1820474032430437914677933 682677762161414218004225)
            ·
              refine ⟨512008321621060663503169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682677762161414218004225 512008321621060663503169)
              ·
                refine ⟨384006241215795497627377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512008321621060663503169 384006241215795497627377)
                ·
                  refine ⟨288004680911846623220533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384006241215795497627377 288004680911846623220533)
                  ·
                    rfl

theorem cell20_630998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_630998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_630998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_630998 prefixEnd_630998 := by exact prefixLift 630998
  have htrace : WordTrace (prefixWord ++ tailWord_630998) baseStart_630998 baseEnd_630998 := by
    simpa [prefixWord, tailWord_630998, baseEnd_630998] using wordTrace_append hprefix tailTrace_630998
  have hstable : (prefixWord ++ tailWord_630998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630998).length < 2 ^ (prefixWord ++ tailWord_630998).sum := by decide
  have hdescent : baseEnd_630998 < baseStart_630998 := by decide
  rcases family_descends (prefixWord ++ tailWord_630998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631013 : List Nat := [1, 3, 1, 4, 2, 1, 3, 5]
def baseStart_631013 : Nat := 118140960795 + 631013 * 2 ^ 59
def prefixEnd_631013 : Nat := 4983230072969 + 3 ^ 40 * 631013 * 2
def baseEnd_631013 : Nat := 96003842440191079240157

theorem tailTrace_631013 : CollatzResearch.WordTrace tailWord_631013 prefixEnd_631013 96003842440191079240157 := by
  unfold tailWord_631013
  simp only [CollatzResearch.WordTrace]
  refine ⟨23014934862955144285625693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15343289908636762857083795 23014934862955144285625693)
  ·
    refine ⟨8630600573608179107109635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23014934862955144285625693 8630600573608179107109635)
    ·
      refine ⟨12945900860412268660664453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630600573608179107109635 12945900860412268660664453)
      ·
        refine ⟨2427356411327300373874585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12945900860412268660664453 2427356411327300373874585)
        ·
          refine ⟨1820517308495475280405939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427356411327300373874585 1820517308495475280405939)
          ·
            refine ⟨2730775962743212920608909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820517308495475280405939 2730775962743212920608909)
            ·
              refine ⟨1024040986028704845228341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2730775962743212920608909 1024040986028704845228341)
              ·
                refine ⟨96003842440191079240157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024040986028704845228341 96003842440191079240157)
                ·
                  rfl

theorem cell20_631013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_631013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631013 prefixEnd_631013 := by exact prefixLift 631013
  have htrace : WordTrace (prefixWord ++ tailWord_631013) baseStart_631013 baseEnd_631013 := by
    simpa [prefixWord, tailWord_631013, baseEnd_631013] using wordTrace_append hprefix tailTrace_631013
  have hstable : (prefixWord ++ tailWord_631013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631013).length < 2 ^ (prefixWord ++ tailWord_631013).sum := by decide
  have hdescent : baseEnd_631013 < baseStart_631013 := by decide
  rcases family_descends (prefixWord ++ tailWord_631013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631020 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_631020 : Nat := 118140960795 + 631020 * 2 ^ 59
def prefixEnd_631020 : Nat := 4983230072969 + 3 ^ 40 * 631020 * 2
def baseEnd_631020 : Nat := 288014722311312324487109

theorem tailTrace_631020 : CollatzResearch.WordTrace tailWord_631020 prefixEnd_631020 288014722311312324487109 := by
  unfold tailWord_631020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11507595086964892240565257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15343460115953189654087009 11507595086964892240565257)
  ·
    refine ⟨8630696315223669180423943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11507595086964892240565257 8630696315223669180423943)
    ·
      refine ⟨12946044472835503770635915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630696315223669180423943 12946044472835503770635915)
      ·
        refine ⟨19419066709253255655953873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12946044472835503770635915 19419066709253255655953873)
        ·
          refine ⟨14564300031939941741965405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19419066709253255655953873 14564300031939941741965405)
          ·
            refine ⟨5461612511977478153237027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14564300031939941741965405 5461612511977478153237027)
            ·
              refine ⟨8192418767966217229855541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461612511977478153237027 8192418767966217229855541)
              ·
                refine ⟨768039259496832865298957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8192418767966217229855541 768039259496832865298957)
                ·
                  refine ⟨288014722311312324487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768039259496832865298957 288014722311312324487109)
                  ·
                    rfl

theorem cell20_631020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_631020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631020 prefixEnd_631020 := by exact prefixLift 631020
  have htrace : WordTrace (prefixWord ++ tailWord_631020) baseStart_631020 baseEnd_631020 := by
    simpa [prefixWord, tailWord_631020, baseEnd_631020] using wordTrace_append hprefix tailTrace_631020
  have hstable : (prefixWord ++ tailWord_631020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631020).length < 2 ^ (prefixWord ++ tailWord_631020).sum := by decide
  have hdescent : baseEnd_631020 < baseStart_631020 := by decide
  rcases family_descends (prefixWord ++ tailWord_631020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631027 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_631027 : Nat := 118140960795 + 631027 * 2 ^ 59
def prefixEnd_631027 : Nat := 4983230072969 + 3 ^ 40 * 631027 * 2
def baseEnd_631027 : Nat := 288017917302051411253747

theorem tailTrace_631027 : CollatzResearch.WordTrace tailWord_631027 prefixEnd_631027 288017917302051411253747 := by
  unfold tailWord_631027
  simp only [CollatzResearch.WordTrace]
  refine ⟨23015445484904424676635335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15343630323269616451090223 23015445484904424676635335)
  ·
    refine ⟨34523168227356637014953003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23015445484904424676635335 34523168227356637014953003)
    ·
      refine ⟨51784752341034955522429505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34523168227356637014953003 51784752341034955522429505)
      ·
        refine ⟨38838564255776216641822129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51784752341034955522429505 38838564255776216641822129)
        ·
          refine ⟨29128923191832162481366597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38838564255776216641822129 29128923191832162481366597)
          ·
            refine ⟨5461673098468530465256237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29128923191832162481366597 5461673098468530465256237)
            ·
              refine ⟨2048127411925698924471089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5461673098468530465256237 2048127411925698924471089)
              ·
                refine ⟨1536095558944274193353317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048127411925698924471089 1536095558944274193353317)
                ·
                  refine ⟨288017917302051411253747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536095558944274193353317 288017917302051411253747)
                  ·
                    rfl

theorem cell20_631027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_631027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631027 prefixEnd_631027 := by exact prefixLift 631027
  have htrace : WordTrace (prefixWord ++ tailWord_631027) baseStart_631027 baseEnd_631027 := by
    simpa [prefixWord, tailWord_631027, baseEnd_631027] using wordTrace_append hprefix tailTrace_631027
  have hstable : (prefixWord ++ tailWord_631027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631027).length < 2 ^ (prefixWord ++ tailWord_631027).sum := by decide
  have hdescent : baseEnd_631027 < baseStart_631027 := by decide
  rcases family_descends (prefixWord ++ tailWord_631027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631075 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 3]
def baseStart_631075 : Nat := 118140960795 + 631075 * 2 ^ 59
def prefixEnd_631075 : Nat := 4983230072969 + 3 ^ 40 * 631075 * 2
def baseEnd_631075 : Nat := 288039825809976577653551

theorem tailTrace_631075 : CollatzResearch.WordTrace tailWord_631075 prefixEnd_631075 288039825809976577653551 := by
  unfold tailWord_631075
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017196188730528874382679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15344797459153685916255119 23017196188730528874382679)
  ·
    refine ⟨34525794283095793311574019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017196188730528874382679 34525794283095793311574019)
    ·
      refine ⟨51788691424643689967361029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34525794283095793311574019 51788691424643689967361029)
      ·
        refine ⟨9710379642120691868880193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51788691424643689967361029 9710379642120691868880193)
        ·
          refine ⟨7282784731590518901660145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9710379642120691868880193 7282784731590518901660145)
          ·
            refine ⟨5462088548692889176245109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7282784731590518901660145 5462088548692889176245109)
            ·
              refine ⟨512070801439958360272979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5462088548692889176245109 512070801439958360272979)
              ·
                refine ⟨768106202159937540409469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512070801439958360272979 768106202159937540409469)
                ·
                  refine ⟨288039825809976577653551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768106202159937540409469 288039825809976577653551)
                  ·
                    rfl

theorem cell20_631075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_631075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631075 prefixEnd_631075 := by exact prefixLift 631075
  have htrace : WordTrace (prefixWord ++ tailWord_631075) baseStart_631075 baseEnd_631075 := by
    simpa [prefixWord, tailWord_631075, baseEnd_631075] using wordTrace_append hprefix tailTrace_631075
  have hstable : (prefixWord ++ tailWord_631075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631075).length < 2 ^ (prefixWord ++ tailWord_631075).sum := by decide
  have hdescent : baseEnd_631075 < baseStart_631075 := by decide
  rcases family_descends (prefixWord ++ tailWord_631075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631089 : List Nat := [1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_631089 : Nat := 118140960795 + 631089 * 2 ^ 59
def prefixEnd_631089 : Nat := 4983230072969 + 3 ^ 40 * 631089 * 2
def baseEnd_631089 : Nat := 96015405263818250395609

theorem tailTrace_631089 : CollatzResearch.WordTrace tailWord_631089 prefixEnd_631089 96015405263818250395609 := by
  unfold tailWord_631089
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017706810679809265392321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15345137873786539510261547 23017706810679809265392321)
  ·
    refine ⟨17263280108009856949044241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23017706810679809265392321 17263280108009856949044241)
    ·
      refine ⟨12947460081007392711783181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17263280108009856949044241 12947460081007392711783181)
      ·
        refine ⟨4855297530377772266918693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12947460081007392711783181 4855297530377772266918693)
        ·
          refine ⟨910368286945832300047255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4855297530377772266918693 910368286945832300047255)
          ·
            refine ⟨1365552430418748450070883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910368286945832300047255 1365552430418748450070883)
            ·
              refine ⟨2048328645628122675106325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365552430418748450070883 2048328645628122675106325)
              ·
                refine ⟨96015405263818250395609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2048328645628122675106325 96015405263818250395609)
                ·
                  rfl

theorem cell20_631089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_631089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631089 prefixEnd_631089 := by exact prefixLift 631089
  have htrace : WordTrace (prefixWord ++ tailWord_631089) baseStart_631089 baseEnd_631089 := by
    simpa [prefixWord, tailWord_631089, baseEnd_631089] using wordTrace_append hprefix tailTrace_631089
  have hstable : (prefixWord ++ tailWord_631089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631089).length < 2 ^ (prefixWord ++ tailWord_631089).sum := by decide
  have hdescent : baseEnd_631089 < baseStart_631089 := by decide
  rcases family_descends (prefixWord ++ tailWord_631089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631120 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_631120 : Nat := 118140960795 + 631120 * 2 ^ 59
def prefixEnd_631120 : Nat := 4983230072969 + 3 ^ 40 * 631120 * 2
def baseEnd_631120 : Nat := 288060365036156421153367

theorem tailTrace_631120 : CollatzResearch.WordTrace tailWord_631120 prefixEnd_631120 288060365036156421153367 := by
  unfold tailWord_631120
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509418736783750779885407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15345891649045001039847209 11509418736783750779885407)
  ·
    refine ⟨17264128105175626169828111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11509418736783750779885407 17264128105175626169828111)
    ·
      refine ⟨25896192157763439254742167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17264128105175626169828111 25896192157763439254742167)
      ·
        refine ⟨38844288236645158882113251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25896192157763439254742167 38844288236645158882113251)
        ·
          refine ⟨58266432354967738323169877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38844288236645158882113251 58266432354967738323169877)
          ·
            refine ⟨682809754159778183474647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 58266432354967738323169877 682809754159778183474647)
            ·
              refine ⟨1024214631239667275211971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682809754159778183474647 1024214631239667275211971)
              ·
                refine ⟨1536321946859500912817957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024214631239667275211971 1536321946859500912817957)
                ·
                  refine ⟨288060365036156421153367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536321946859500912817957 288060365036156421153367)
                  ·
                    rfl

theorem cell20_631120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_631120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631120 prefixEnd_631120 := by exact prefixLift 631120
  have htrace : WordTrace (prefixWord ++ tailWord_631120) baseStart_631120 baseEnd_631120 := by
    simpa [prefixWord, tailWord_631120, baseEnd_631120] using wordTrace_append hprefix tailTrace_631120
  have hstable : (prefixWord ++ tailWord_631120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631120).length < 2 ^ (prefixWord ++ tailWord_631120).sum := by decide
  have hdescent : baseEnd_631120 < baseStart_631120 := by decide
  rcases family_descends (prefixWord ++ tailWord_631120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631171 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 2]
def baseStart_631171 : Nat := 118140960795 + 631171 * 2 ^ 59
def prefixEnd_631171 : Nat := 4983230072969 + 3 ^ 40 * 631171 * 2
def baseEnd_631171 : Nat := 288083642825826910453159

theorem tailTrace_631171 : CollatzResearch.WordTrace tailWord_631171 prefixEnd_631171 288083642825826910453159 := by
  unfold tailWord_631171
  simp only [CollatzResearch.WordTrace]
  refine ⟨23020697596382737269877367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15347131730921824846584911 23020697596382737269877367)
  ·
    refine ⟨34531046394574105904816051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23020697596382737269877367 34531046394574105904816051)
    ·
      refine ⟨51796569591861158857224077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34531046394574105904816051 51796569591861158857224077)
      ·
        refine ⟨19423713596947934571459029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51796569591861158857224077 19423713596947934571459029)
        ·
          refine ⟨455243287428467216518571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19423713596947934571459029 455243287428467216518571)
          ·
            refine ⟨682864931142700824777857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455243287428467216518571 682864931142700824777857)
            ·
              refine ⟨512148698357025618583393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682864931142700824777857 512148698357025618583393)
              ·
                refine ⟨384111523767769213937545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512148698357025618583393 384111523767769213937545)
                ·
                  refine ⟨288083642825826910453159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384111523767769213937545 288083642825826910453159)
                  ·
                    rfl

theorem cell20_631171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 2].length) (baseStart_631171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631171 prefixEnd_631171 := by exact prefixLift 631171
  have htrace : WordTrace (prefixWord ++ tailWord_631171) baseStart_631171 baseEnd_631171 := by
    simpa [prefixWord, tailWord_631171, baseEnd_631171] using wordTrace_append hprefix tailTrace_631171
  have hstable : (prefixWord ++ tailWord_631171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631171).length < 2 ^ (prefixWord ++ tailWord_631171).sum := by decide
  have hdescent : baseEnd_631171 < baseStart_631171 := by decide
  rcases family_descends (prefixWord ++ tailWord_631171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631182 : List Nat := [4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_631182 : Nat := 118140960795 + 631182 * 2 ^ 59
def prefixEnd_631182 : Nat := 4983230072969 + 3 ^ 40 * 631182 * 2
def baseEnd_631182 : Nat := 96029554508519920362149

theorem tailTrace_631182 : CollatzResearch.WordTrace tailWord_631182 prefixEnd_631182 96029554508519920362149 := by
  unfold tailWord_631182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877637349917860768565975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15347399199561924099018533 2877637349917860768565975)
  ·
    refine ⟨4316456024876791152848963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877637349917860768565975 4316456024876791152848963)
    ·
      refine ⟨6474684037315186729273445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316456024876791152848963 6474684037315186729273445)
      ·
        refine ⟨1214003256996597511738771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6474684037315186729273445 1214003256996597511738771)
        ·
          refine ⟨1821004885494896267608157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214003256996597511738771 1821004885494896267608157)
          ·
            refine ⟨682876832060586100353059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1821004885494896267608157 682876832060586100353059)
            ·
              refine ⟨1024315248090879150529589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682876832060586100353059 1024315248090879150529589)
              ·
                refine ⟨96029554508519920362149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024315248090879150529589 96029554508519920362149)
                ·
                  rfl

theorem cell20_631182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_631182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631182 prefixEnd_631182 := by exact prefixLift 631182
  have htrace : WordTrace (prefixWord ++ tailWord_631182) baseStart_631182 baseEnd_631182 := by
    simpa [prefixWord, tailWord_631182, baseEnd_631182] using wordTrace_append hprefix tailTrace_631182
  have hstable : (prefixWord ++ tailWord_631182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631182).length < 2 ^ (prefixWord ++ tailWord_631182).sum := by decide
  have hdescent : baseEnd_631182 < baseStart_631182 := by decide
  rcases family_descends (prefixWord ++ tailWord_631182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631203 : List Nat := [1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_631203 : Nat := 118140960795 + 631203 * 2 ^ 59
def prefixEnd_631203 : Nat := 4983230072969 + 3 ^ 40 * 631203 * 2
def baseEnd_631203 : Nat := 96032749499259007128787

theorem tailTrace_631203 : CollatzResearch.WordTrace tailWord_631203 prefixEnd_631203 96032749499259007128787 := by
  unfold tailWord_631203
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021864732266806735042263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15347909821511204490028175 23021864732266806735042263)
  ·
    refine ⟨34532797098400210102563395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23021864732266806735042263 34532797098400210102563395)
    ·
      refine ⟨51799195647600315153845093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34532797098400210102563395 51799195647600315153845093)
      ·
        refine ⟨9712349183925059091345955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51799195647600315153845093 9712349183925059091345955)
        ·
          refine ⟨14568523775887588637018933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712349183925059091345955 14568523775887588637018933)
          ·
            refine ⟨1365799103989461434720525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14568523775887588637018933 1365799103989461434720525)
            ·
              refine ⟨512174663996048038020197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1365799103989461434720525 512174663996048038020197)
              ·
                refine ⟨96032749499259007128787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512174663996048038020197 96032749499259007128787)
                ·
                  rfl

theorem cell20_631203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_631203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631203 prefixEnd_631203 := by exact prefixLift 631203
  have htrace : WordTrace (prefixWord ++ tailWord_631203) baseStart_631203 baseEnd_631203 := by
    simpa [prefixWord, tailWord_631203, baseEnd_631203] using wordTrace_append hprefix tailTrace_631203
  have hstable : (prefixWord ++ tailWord_631203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631203).length < 2 ^ (prefixWord ++ tailWord_631203).sum := by decide
  have hdescent : baseEnd_631203 < baseStart_631203 := by decide
  rcases family_descends (prefixWord ++ tailWord_631203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631244 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_631244 : Nat := 118140960795 + 631244 * 2 ^ 59
def prefixEnd_631244 : Nat := 4983230072969 + 3 ^ 40 * 631244 * 2
def baseEnd_631244 : Nat := 288116962014963101019527

theorem tailTrace_631244 : CollatzResearch.WordTrace tailWord_631244 prefixEnd_631244 288116962014963101019527 := by
  unfold tailWord_631244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511680062559135368642393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15348906750078847158189857 11511680062559135368642393)
  ·
    refine ⟨8633760046919351526481795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11511680062559135368642393 8633760046919351526481795)
    ·
      refine ⟨12950640070379027289722693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633760046919351526481795 12950640070379027289722693)
      ·
        refine ⟨2428245013196067616823005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12950640070379027289722693 2428245013196067616823005)
        ·
          refine ⟨910591879948525356308627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2428245013196067616823005 910591879948525356308627)
          ·
            refine ⟨1365887819922788034462941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910591879948525356308627 1365887819922788034462941)
            ·
              refine ⟨512207932471045512923603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1365887819922788034462941 512207932471045512923603)
              ·
                refine ⟨768311898706568269385405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512207932471045512923603 768311898706568269385405)
                ·
                  refine ⟨288116962014963101019527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768311898706568269385405 288116962014963101019527)
                  ·
                    rfl

theorem cell20_631244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_631244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631244 prefixEnd_631244 := by exact prefixLift 631244
  have htrace : WordTrace (prefixWord ++ tailWord_631244) baseStart_631244 baseEnd_631244 := by
    simpa [prefixWord, tailWord_631244, baseEnd_631244] using wordTrace_append hprefix tailTrace_631244
  have hstable : (prefixWord ++ tailWord_631244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631244).length < 2 ^ (prefixWord ++ tailWord_631244).sum := by decide
  have hdescent : baseEnd_631244 < baseStart_631244 := by decide
  rcases family_descends (prefixWord ++ tailWord_631244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631285 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 2]
def baseStart_631285 : Nat := 118140960795 + 631285 * 2 ^ 59
def prefixEnd_631285 : Nat := 4983230072969 + 3 ^ 40 * 631285 * 2
def baseEnd_631285 : Nat := 288135675532149180652693

theorem tailTrace_631285 : CollatzResearch.WordTrace tailWord_631285 prefixEnd_631285 288135675532149180652693 := by
  unfold tailWord_631285
  simp only [CollatzResearch.WordTrace]
  refine ⟨23024855517969734739527309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15349903678646489826351539 23024855517969734739527309)
  ·
    refine ⟨8634320819238650527322741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23024855517969734739527309 8634320819238650527322741)
    ·
      refine ⟨809467576803623486936507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8634320819238650527322741 809467576803623486936507)
      ·
        refine ⟨1214201365205435230404761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809467576803623486936507 1214201365205435230404761)
        ·
          refine ⟨910651023904076422803571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214201365205435230404761 910651023904076422803571)
          ·
            refine ⟨1365976535856114634205357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910651023904076422803571 1365976535856114634205357)
            ·
              refine ⟨512241200946042987827009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1365976535856114634205357 512241200946042987827009)
              ·
                refine ⟨384180900709532240870257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512241200946042987827009 384180900709532240870257)
                ·
                  refine ⟨288135675532149180652693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384180900709532240870257 288135675532149180652693)
                  ·
                    rfl

theorem cell20_631285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_631285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631285 prefixEnd_631285 := by exact prefixLift 631285
  have htrace : WordTrace (prefixWord ++ tailWord_631285) baseStart_631285 baseEnd_631285 := by
    simpa [prefixWord, tailWord_631285, baseEnd_631285] using wordTrace_append hprefix tailTrace_631285
  have hstable : (prefixWord ++ tailWord_631285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631285).length < 2 ^ (prefixWord ++ tailWord_631285).sum := by decide
  have hdescent : baseEnd_631285 < baseStart_631285 := by decide
  rcases family_descends (prefixWord ++ tailWord_631285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631286 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_631286 : Nat := 118140960795 + 631286 * 2 ^ 59
def prefixEnd_631286 : Nat := 4983230072969 + 3 ^ 40 * 631286 * 2
def baseEnd_631286 : Nat := 288136131959397621619355

theorem tailTrace_631286 : CollatzResearch.WordTrace tailWord_631286 prefixEnd_631286 288136131959397621619355 := by
  unfold tailWord_631286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439055749435381994394607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15349927993977407940209141 1439055749435381994394607)
  ·
    refine ⟨2158583624153072991591911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1439055749435381994394607 2158583624153072991591911)
    ·
      refine ⟨3237875436229609487387867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158583624153072991591911 3237875436229609487387867)
      ·
        refine ⟨4856813154344414231081801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237875436229609487387867 4856813154344414231081801)
        ·
          refine ⟨3642609865758310673311351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856813154344414231081801 3642609865758310673311351)
          ·
            refine ⟨5463914798637466009967027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642609865758310673311351 5463914798637466009967027)
            ·
              refine ⟨8195872197956199014950541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463914798637466009967027 8195872197956199014950541)
              ·
                refine ⟨3073452074233574630606453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8195872197956199014950541 3073452074233574630606453)
                ·
                  refine ⟨288136131959397621619355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073452074233574630606453 288136131959397621619355)
                  ·
                    rfl

theorem cell20_631286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_631286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631286 prefixEnd_631286 := by exact prefixLift 631286
  have htrace : WordTrace (prefixWord ++ tailWord_631286) baseStart_631286 baseEnd_631286 := by
    simpa [prefixWord, tailWord_631286, baseEnd_631286] using wordTrace_append hprefix tailTrace_631286
  have hstable : (prefixWord ++ tailWord_631286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631286).length < 2 ^ (prefixWord ++ tailWord_631286).sum := by decide
  have hdescent : baseEnd_631286 < baseStart_631286 := by decide
  rcases family_descends (prefixWord ++ tailWord_631286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631303 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_631303 : Nat := 118140960795 + 631303 * 2 ^ 59
def prefixEnd_631303 : Nat := 4983230072969 + 3 ^ 40 * 631303 * 2
def baseEnd_631303 : Nat := 288143891222621118052619

theorem tailTrace_631303 : CollatzResearch.WordTrace tailWord_631303 prefixEnd_631303 288143891222621118052619 := by
  unfold tailWord_631303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23025512031904523813682563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15350341354603015875788375 23025512031904523813682563)
  ·
    refine ⟨34538268047856785720523845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23025512031904523813682563 34538268047856785720523845)
    ·
      refine ⟨6475925258973147322598221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34538268047856785720523845 6475925258973147322598221)
      ·
        refine ⟨2428471972114930245974333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6475925258973147322598221 2428471972114930245974333)
        ·
          refine ⟨910676989543098842240375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2428471972114930245974333 910676989543098842240375)
          ·
            refine ⟨1366015484314648263360563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910676989543098842240375 1366015484314648263360563)
            ·
              refine ⟨2049023226471972395040845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366015484314648263360563 2049023226471972395040845)
              ·
                refine ⟨768383709926989648140317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2049023226471972395040845 768383709926989648140317)
                ·
                  refine ⟨288143891222621118052619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768383709926989648140317 288143891222621118052619)
                  ·
                    rfl

theorem cell20_631303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_631303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631303 prefixEnd_631303 := by exact prefixLift 631303
  have htrace : WordTrace (prefixWord ++ tailWord_631303) baseStart_631303 baseEnd_631303 := by
    simpa [prefixWord, tailWord_631303, baseEnd_631303] using wordTrace_append hprefix tailTrace_631303
  have hstable : (prefixWord ++ tailWord_631303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631303).length < 2 ^ (prefixWord ++ tailWord_631303).sum := by decide
  have hdescent : baseEnd_631303 < baseStart_631303 := by decide
  rcases family_descends (prefixWord ++ tailWord_631303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631338 : List Nat := [3, 1, 4, 1, 1, 10]
def baseStart_631338 : Nat := 118140960795 + 631338 * 2 ^ 59
def prefixEnd_631338 : Nat := 4983230072969 + 3 ^ 40 * 631338 * 2
def baseEnd_631338 : Nat := 10672587636159872292067

theorem tailTrace_631338 : CollatzResearch.WordTrace tailWord_631338 prefixEnd_631338 10672587636159872292067 := by
  unfold tailWord_631338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756697146694431197801667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15351192391185149860804445 5756697146694431197801667)
  ·
    refine ⟨8635045720041646796702501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5756697146694431197801667 8635045720041646796702501)
    ·
      refine ⟨1619071072507808774381719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8635045720041646796702501 1619071072507808774381719)
      ·
        refine ⟨2428606608761713161572579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619071072507808774381719 2428606608761713161572579)
        ·
          refine ⟨3642909913142569742358869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428606608761713161572579 3642909913142569742358869)
          ·
            refine ⟨10672587636159872292067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3642909913142569742358869 10672587636159872292067)
            ·
              rfl

theorem cell20_631338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 10].length) (baseStart_631338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631338 prefixEnd_631338 := by exact prefixLift 631338
  have htrace : WordTrace (prefixWord ++ tailWord_631338) baseStart_631338 baseEnd_631338 := by
    simpa [prefixWord, tailWord_631338, baseEnd_631338] using wordTrace_append hprefix tailTrace_631338
  have hstable : (prefixWord ++ tailWord_631338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631338).length < 2 ^ (prefixWord ++ tailWord_631338).sum := by decide
  have hdescent : baseEnd_631338 < baseStart_631338 := by decide
  rcases family_descends (prefixWord ++ tailWord_631338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631345 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_631345 : Nat := 118140960795 + 631345 * 2 ^ 59
def prefixEnd_631345 : Nat := 4983230072969 + 3 ^ 40 * 631345 * 2
def baseEnd_631345 : Nat := 288163061167055638652447

theorem tailTrace_631345 : CollatzResearch.WordTrace tailWord_631345 prefixEnd_631345 288163061167055638652447 := by
  unfold tailWord_631345
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027043897752364986711489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15351362598501576657807659 23027043897752364986711489)
  ·
    refine ⟨17270282923314273740033617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23027043897752364986711489 17270282923314273740033617)
    ·
      refine ⟨12952712192485705305025213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17270282923314273740033617 12952712192485705305025213)
      ·
        refine ⟨4857267072182139489384455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12952712192485705305025213 4857267072182139489384455)
        ·
          refine ⟨7285900608273209234076683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857267072182139489384455 7285900608273209234076683)
          ·
            refine ⟨10928850912409813851115025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285900608273209234076683 10928850912409813851115025)
            ·
              refine ⟨8196638184307360388336269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10928850912409813851115025 8196638184307360388336269)
              ·
                refine ⟨3073739319115260145626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8196638184307360388336269 3073739319115260145626101)
                ·
                  refine ⟨288163061167055638652447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073739319115260145626101 288163061167055638652447)
                  ·
                    rfl

theorem cell20_631345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_631345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631345 prefixEnd_631345 := by exact prefixLift 631345
  have htrace : WordTrace (prefixWord ++ tailWord_631345) baseStart_631345 baseEnd_631345 := by
    simpa [prefixWord, tailWord_631345, baseEnd_631345] using wordTrace_append hprefix tailTrace_631345
  have hstable : (prefixWord ++ tailWord_631345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631345).length < 2 ^ (prefixWord ++ tailWord_631345).sum := by decide
  have hdescent : baseEnd_631345 < baseStart_631345 := by decide
  rcases family_descends (prefixWord ++ tailWord_631345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631383 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_631383 : Nat := 118140960795 + 631383 * 2 ^ 59
def prefixEnd_631383 : Nat := 4983230072969 + 3 ^ 40 * 631383 * 2
def baseEnd_631383 : Nat := 288180405402496395385625

theorem tailTrace_631383 : CollatzResearch.WordTrace tailWord_631383 prefixEnd_631383 288180405402496395385625 := by
  unfold tailWord_631383
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028429871614697476594803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15352286581076464984396535 23028429871614697476594803)
  ·
    refine ⟨34542644807422046214892205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028429871614697476594803 34542644807422046214892205)
    ·
      refine ⟨12953491802783267330584577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34542644807422046214892205 12953491802783267330584577)
      ·
        refine ⟨9715118852087450497938433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12953491802783267330584577 9715118852087450497938433)
        ·
          refine ⟨7286339139065587873453825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9715118852087450497938433 7286339139065587873453825)
          ·
            refine ⟨5464754354299190905090369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286339139065587873453825 5464754354299190905090369)
            ·
              refine ⟨4098565765724393178817777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464754354299190905090369 4098565765724393178817777)
              ·
                refine ⟨3073924324293294884113333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098565765724393178817777 3073924324293294884113333)
                ·
                  refine ⟨288180405402496395385625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073924324293294884113333 288180405402496395385625)
                  ·
                    rfl

theorem cell20_631383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_631383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631383 prefixEnd_631383 := by exact prefixLift 631383
  have htrace : WordTrace (prefixWord ++ tailWord_631383) baseStart_631383 baseEnd_631383 := by
    simpa [prefixWord, tailWord_631383, baseEnd_631383] using wordTrace_append hprefix tailTrace_631383
  have hstable : (prefixWord ++ tailWord_631383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631383).length < 2 ^ (prefixWord ++ tailWord_631383).sum := by decide
  have hdescent : baseEnd_631383 < baseStart_631383 := by decide
  rcases family_descends (prefixWord ++ tailWord_631383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631417 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 3]
def baseStart_631417 : Nat := 118140960795 + 631417 * 2 ^ 59
def prefixEnd_631417 : Nat := 4983230072969 + 3 ^ 40 * 631417 * 2
def baseEnd_631417 : Nat := 288195923928943388252153

theorem tailTrace_631417 : CollatzResearch.WordTrace tailWord_631417 prefixEnd_631417 288195923928943388252153 := by
  unfold tailWord_631417
  simp only [CollatzResearch.WordTrace]
  refine ⟨23029669953491521283332505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15353113302327680855555003 23029669953491521283332505)
  ·
    refine ⟨17272252465118640962499379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23029669953491521283332505 17272252465118640962499379)
    ·
      refine ⟨25908378697677961443749069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17272252465118640962499379 25908378697677961443749069)
      ·
        refine ⟨9715642011629235541405901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25908378697677961443749069 9715642011629235541405901)
        ·
          refine ⟨3643365754360963328027213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9715642011629235541405901 3643365754360963328027213)
          ·
            refine ⟨1366262157885361248010205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3643365754360963328027213 1366262157885361248010205)
            ·
              refine ⟨512348309207010468003827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1366262157885361248010205 512348309207010468003827)
              ·
                refine ⟨768522463810515702005741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512348309207010468003827 768522463810515702005741)
                ·
                  refine ⟨288195923928943388252153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768522463810515702005741 288195923928943388252153)
                  ·
                    rfl

theorem cell20_631417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_631417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631417 prefixEnd_631417 := by exact prefixLift 631417
  have htrace : WordTrace (prefixWord ++ tailWord_631417) baseStart_631417 baseEnd_631417 := by
    simpa [prefixWord, tailWord_631417, baseEnd_631417] using wordTrace_append hprefix tailTrace_631417
  have hstable : (prefixWord ++ tailWord_631417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631417).length < 2 ^ (prefixWord ++ tailWord_631417).sum := by decide
  have hdescent : baseEnd_631417 < baseStart_631417 := by decide
  rcases family_descends (prefixWord ++ tailWord_631417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631452 : List Nat := [2, 2, 3, 2, 2, 1, 8]
def baseStart_631452 : Nat := 118140960795 + 631452 * 2 ^ 59
def prefixEnd_631452 : Nat := 4983230072969 + 3 ^ 40 * 631452 * 2
def baseEnd_631452 : Nat := 32023544320293202453927

theorem tailTrace_631452 : CollatzResearch.WordTrace tailWord_631452 prefixEnd_631452 32023544320293202453927 := by
  unfold tailWord_631452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515473254182361130428305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15353964338909814840571073 11515473254182361130428305)
  ·
    refine ⟨8636604940636770847821229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11515473254182361130428305 8636604940636770847821229)
    ·
      refine ⟨3238726852738789067932961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8636604940636770847821229 3238726852738789067932961)
      ·
        refine ⟨2429045139554091800949721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3238726852738789067932961 2429045139554091800949721)
        ·
          refine ⟨1821783854665568850712291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429045139554091800949721 1821783854665568850712291)
          ·
            refine ⟨2732675781998353276068437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821783854665568850712291 2732675781998353276068437)
            ·
              refine ⟨32023544320293202453927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2732675781998353276068437 32023544320293202453927)
              ·
                rfl

theorem cell20_631452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_631452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631452 prefixEnd_631452 := by exact prefixLift 631452
  have htrace : WordTrace (prefixWord ++ tailWord_631452) baseStart_631452 baseEnd_631452 := by
    simpa [prefixWord, tailWord_631452, baseEnd_631452] using wordTrace_append hprefix tailTrace_631452
  have hstable : (prefixWord ++ tailWord_631452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631452).length < 2 ^ (prefixWord ++ tailWord_631452).sum := by decide
  have hdescent : baseEnd_631452 < baseStart_631452 := by decide
  rcases family_descends (prefixWord ++ tailWord_631452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631469 : List Nat := [1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_631469 : Nat := 118140960795 + 631469 * 2 ^ 59
def prefixEnd_631469 : Nat := 4983230072969 + 3 ^ 40 * 631469 * 2
def baseEnd_631469 : Nat := 96073219381954106172869

theorem tailTrace_631469 : CollatzResearch.WordTrace tailWord_631469 prefixEnd_631469 96073219381954106172869 := by
  unfold tailWord_631469
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031566549303134164225461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15354377699535422776150307 23031566549303134164225461)
  ·
    refine ⟨2159209363997168827896137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23031566549303134164225461 2159209363997168827896137)
    ·
      refine ⟨1619407022997876620922103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2159209363997168827896137 1619407022997876620922103)
      ·
        refine ⟨2429110534496814931383155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619407022997876620922103 2429110534496814931383155)
        ·
          refine ⟨3643665801745222397074733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429110534496814931383155 3643665801745222397074733)
          ·
            refine ⟨1366374675654458398903025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3643665801745222397074733 1366374675654458398903025)
            ·
              refine ⟨1024781006740843799177269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366374675654458398903025 1024781006740843799177269)
              ·
                refine ⟨96073219381954106172869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024781006740843799177269 96073219381954106172869)
                ·
                  rfl

theorem cell20_631469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_631469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631469 prefixEnd_631469 := by exact prefixLift 631469
  have htrace : WordTrace (prefixWord ++ tailWord_631469) baseStart_631469 baseEnd_631469 := by
    simpa [prefixWord, tailWord_631469, baseEnd_631469] using wordTrace_append hprefix tailTrace_631469
  have hstable : (prefixWord ++ tailWord_631469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631469).length < 2 ^ (prefixWord ++ tailWord_631469).sum := by decide
  have hdescent : baseEnd_631469 < baseStart_631469 := by decide
  rcases family_descends (prefixWord ++ tailWord_631469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631511 : List Nat := [1, 1, 3, 2, 1, 12]
def baseStart_631511 : Nat := 118140960795 + 631511 * 2 ^ 59
def prefixEnd_631511 : Nat := 4983230072969 + 3 ^ 40 * 631511 * 2
def baseEnd_631511 : Nat := 10675512151492475522905

theorem tailTrace_631511 : CollatzResearch.WordTrace tailWord_631511 prefixEnd_631511 10675512151492475522905 := by
  unfold tailWord_631511
  simp only [CollatzResearch.WordTrace]
  refine ⟨23033098415150975337254387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15355398943433983558169591 23033098415150975337254387)
  ·
    refine ⟨34549647622726463005881581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23033098415150975337254387 34549647622726463005881581)
    ·
      refine ⟨12956117858522423627205593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34549647622726463005881581 12956117858522423627205593)
      ·
        refine ⟨9717088393891817720404195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12956117858522423627205593 9717088393891817720404195)
        ·
          refine ⟨14575632590837726580606293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9717088393891817720404195 14575632590837726580606293)
          ·
            refine ⟨10675512151492475522905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14575632590837726580606293 10675512151492475522905)
            ·
              rfl

theorem cell20_631511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 12].length) (baseStart_631511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631511 prefixEnd_631511 := by exact prefixLift 631511
  have htrace : WordTrace (prefixWord ++ tailWord_631511) baseStart_631511 baseEnd_631511 := by
    simpa [prefixWord, tailWord_631511, baseEnd_631511] using wordTrace_append hprefix tailTrace_631511
  have hstable : (prefixWord ++ tailWord_631511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631511).length < 2 ^ (prefixWord ++ tailWord_631511).sum := by decide
  have hdescent : baseEnd_631511 < baseStart_631511 := by decide
  rcases family_descends (prefixWord ++ tailWord_631511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631514 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_631514 : Nat := 118140960795 + 631514 * 2 ^ 59
def prefixEnd_631514 : Nat := 4983230072969 + 3 ^ 40 * 631514 * 2
def baseEnd_631514 : Nat := 288240197372042162018423

theorem tailTrace_631514 : CollatzResearch.WordTrace tailWord_631514 prefixEnd_631514 288240197372042162018423 := by
  unfold tailWord_631514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758301958535026712403399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15355471889426737899742397 5758301958535026712403399)
  ·
    refine ⟨8637452937802540068605099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5758301958535026712403399 8637452937802540068605099)
    ·
      refine ⟨12956179406703810102907649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8637452937802540068605099 12956179406703810102907649)
      ·
        refine ⟨9717134555027857577180737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12956179406703810102907649 9717134555027857577180737)
        ·
          refine ⟨7287850916270893182885553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9717134555027857577180737 7287850916270893182885553)
          ·
            refine ⟨5465888187203169887164165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7287850916270893182885553 5465888187203169887164165)
            ·
              refine ⟨1024854035100594353843281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5465888187203169887164165 1024854035100594353843281)
              ·
                refine ⟨768640526325445765382461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024854035100594353843281 768640526325445765382461)
                ·
                  refine ⟨288240197372042162018423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768640526325445765382461 288240197372042162018423)
                  ·
                    rfl

theorem cell20_631514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_631514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631514 prefixEnd_631514 := by exact prefixLift 631514
  have htrace : WordTrace (prefixWord ++ tailWord_631514) baseStart_631514 baseEnd_631514 := by
    simpa [prefixWord, tailWord_631514, baseEnd_631514] using wordTrace_append hprefix tailTrace_631514
  have hstable : (prefixWord ++ tailWord_631514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631514).length < 2 ^ (prefixWord ++ tailWord_631514).sum := by decide
  have hdescent : baseEnd_631514 < baseStart_631514 := by decide
  rcases family_descends (prefixWord ++ tailWord_631514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631573 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_631573 : Nat := 118140960795 + 631573 * 2 ^ 59
def prefixEnd_631573 : Nat := 4983230072969 + 3 ^ 40 * 631573 * 2
def baseEnd_631573 : Nat := 288267126579700179051515

theorem tailTrace_631573 : CollatzResearch.WordTrace tailWord_631573 prefixEnd_631573 288267126579700179051515 := by
  unfold tailWord_631573
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035359740926359926011373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15356906493950906617340915 23035359740926359926011373)
  ·
    refine ⟨8638259902847384972254265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23035359740926359926011373 8638259902847384972254265)
    ·
      refine ⟨6478694927135538729190699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8638259902847384972254265 6478694927135538729190699)
      ·
        refine ⟨9718042390703308093786049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6478694927135538729190699 9718042390703308093786049)
        ·
          refine ⟨7288531793027481070339537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9718042390703308093786049 7288531793027481070339537)
          ·
            refine ⟨5466398844770610802754653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288531793027481070339537 5466398844770610802754653)
            ·
              refine ⟨2049899566788979051032995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5466398844770610802754653 2049899566788979051032995)
              ·
                refine ⟨3074849350183468576549493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049899566788979051032995 3074849350183468576549493)
                ·
                  refine ⟨288267126579700179051515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3074849350183468576549493 288267126579700179051515)
                  ·
                    rfl

theorem cell20_631573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_631573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631573 prefixEnd_631573 := by exact prefixLift 631573
  have htrace : WordTrace (prefixWord ++ tailWord_631573) baseStart_631573 baseEnd_631573 := by
    simpa [prefixWord, tailWord_631573, baseEnd_631573] using wordTrace_append hprefix tailTrace_631573
  have hstable : (prefixWord ++ tailWord_631573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631573).length < 2 ^ (prefixWord ++ tailWord_631573).sum := by decide
  have hdescent : baseEnd_631573 < baseStart_631573 := by decide
  rcases family_descends (prefixWord ++ tailWord_631573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631587 : List Nat := [1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_631587 : Nat := 118140960795 + 631587 * 2 ^ 59
def prefixEnd_631587 : Nat := 4983230072969 + 3 ^ 40 * 631587 * 2
def baseEnd_631587 : Nat := 96091172187059450861597

theorem tailTrace_631587 : CollatzResearch.WordTrace tailWord_631587 prefixEnd_631587 96091172187059450861597 := by
  unfold tailWord_631587
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035870362875640317021015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15357246908583760211347343 23035870362875640317021015)
  ·
    refine ⟨34553805544313460475531523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23035870362875640317021015 34553805544313460475531523)
    ·
      refine ⟨51830708316470190713297285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34553805544313460475531523 51830708316470190713297285)
      ·
        refine ⟨9718257809338160758743241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51830708316470190713297285 9718257809338160758743241)
        ·
          refine ⟨7288693357003620569057431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9718257809338160758743241 7288693357003620569057431)
          ·
            refine ⟨10933040035505430853586147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288693357003620569057431 10933040035505430853586147)
            ·
              refine ⟨16399560053258146280379221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10933040035505430853586147 16399560053258146280379221)
              ·
                refine ⟨96091172187059450861597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16399560053258146280379221 96091172187059450861597)
                ·
                  rfl

theorem cell20_631587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_631587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631587 prefixEnd_631587 := by exact prefixLift 631587
  have htrace : WordTrace (prefixWord ++ tailWord_631587) baseStart_631587 baseEnd_631587 := by
    simpa [prefixWord, tailWord_631587, baseEnd_631587] using wordTrace_append hprefix tailTrace_631587
  have hstable : (prefixWord ++ tailWord_631587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631587).length < 2 ^ (prefixWord ++ tailWord_631587).sum := by decide
  have hdescent : baseEnd_631587 < baseStart_631587 := by decide
  rcases family_descends (prefixWord ++ tailWord_631587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631610 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_631610 : Nat := 118140960795 + 631610 * 2 ^ 59
def prefixEnd_631610 : Nat := 4983230072969 + 3 ^ 40 * 631610 * 2
def baseEnd_631610 : Nat := 288284014387892494818031

theorem tailTrace_631610 : CollatzResearch.WordTrace tailWord_631610 prefixEnd_631610 288284014387892494818031 := by
  unfold tailWord_631610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759177310448078811277071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15357806161194876830072189 5759177310448078811277071)
  ·
    refine ⟨8638765965672118216915607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5759177310448078811277071 8638765965672118216915607)
    ·
      refine ⟨12958148948508177325373411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8638765965672118216915607 12958148948508177325373411)
      ·
        refine ⟨19437223422762265988060117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12958148948508177325373411 19437223422762265988060117)
        ·
          refine ⟨455559923970990609095159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19437223422762265988060117 455559923970990609095159)
          ·
            refine ⟨683339885956485913642739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455559923970990609095159 683339885956485913642739)
            ·
              refine ⟨1025009828934728870464109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683339885956485913642739 1025009828934728870464109)
              ·
                refine ⟨384378685850523326424041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1025009828934728870464109 384378685850523326424041)
                ·
                  refine ⟨288284014387892494818031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384378685850523326424041 288284014387892494818031)
                  ·
                    rfl

theorem cell20_631610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_631610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631610 prefixEnd_631610 := by exact prefixLift 631610
  have htrace : WordTrace (prefixWord ++ tailWord_631610) baseStart_631610 baseEnd_631610 := by
    simpa [prefixWord, tailWord_631610, baseEnd_631610] using wordTrace_append hprefix tailTrace_631610
  have hstable : (prefixWord ++ tailWord_631610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631610).length < 2 ^ (prefixWord ++ tailWord_631610).sum := by decide
  have hdescent : baseEnd_631610 < baseStart_631610 := by decide
  rcases family_descends (prefixWord ++ tailWord_631610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631625 : List Nat := [1, 2, 1, 1, 2, 5, 8]
def baseStart_631625 : Nat := 118140960795 + 631625 * 2 ^ 59
def prefixEnd_631625 : Nat := 4983230072969 + 3 ^ 40 * 631625 * 2
def baseEnd_631625 : Nat := 32032317866291012146441

theorem tailTrace_631625 : CollatzResearch.WordTrace tailWord_631625 prefixEnd_631625 32032317866291012146441 := by
  unfold tailWord_631625
  simp only [CollatzResearch.WordTrace]
  refine ⟨23037256336737972806904329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15358170891158648537936219 23037256336737972806904329)
  ·
    refine ⟨17277942252553479605178247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23037256336737972806904329 17277942252553479605178247)
    ·
      refine ⟨25916913378830219407767371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17277942252553479605178247 25916913378830219407767371)
      ·
        refine ⟨38875370068245329111651057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25916913378830219407767371 38875370068245329111651057)
        ·
          refine ⟨29156527551183996833738293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38875370068245329111651057 29156527551183996833738293)
          ·
            refine ⟨2733424457923499703162965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29156527551183996833738293 2733424457923499703162965)
            ·
              refine ⟨32032317866291012146441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2733424457923499703162965 32032317866291012146441)
              ·
                rfl

theorem cell20_631625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_631625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631625 prefixEnd_631625 := by exact prefixLift 631625
  have htrace : WordTrace (prefixWord ++ tailWord_631625) baseStart_631625 baseEnd_631625 := by
    simpa [prefixWord, tailWord_631625, baseEnd_631625] using wordTrace_append hprefix tailTrace_631625
  have hstable : (prefixWord ++ tailWord_631625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631625).length < 2 ^ (prefixWord ++ tailWord_631625).sum := by decide
  have hdescent : baseEnd_631625 < baseStart_631625 := by decide
  rcases family_descends (prefixWord ++ tailWord_631625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631635 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 2]
def baseStart_631635 : Nat := 118140960795 + 631635 * 2 ^ 59
def prefixEnd_631635 : Nat := 4983230072969 + 3 ^ 40 * 631635 * 2
def baseEnd_631635 : Nat := 288295425069103518984595

theorem tailTrace_631635 : CollatzResearch.WordTrace tailWord_631635 prefixEnd_631635 288295425069103518984595 := by
  unfold tailWord_631635
  simp only [CollatzResearch.WordTrace]
  refine ⟨23037621066701744514768359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15358414044467829676512239 23037621066701744514768359)
  ·
    refine ⟨34556431600052616772152539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23037621066701744514768359 34556431600052616772152539)
    ·
      refine ⟨51834647400078925158228809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34556431600052616772152539 51834647400078925158228809)
      ·
        refine ⟨38875985550059193868671607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51834647400078925158228809 38875985550059193868671607)
        ·
          refine ⟨58313978325088790803007411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38875985550059193868671607 58313978325088790803007411)
          ·
            refine ⟨87470967487633186204511117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58313978325088790803007411 87470967487633186204511117)
            ·
              refine ⟨32801612807862444826691669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87470967487633186204511117 32801612807862444826691669)
              ·
                refine ⟨384393900092138025312793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32801612807862444826691669 384393900092138025312793)
                ·
                  refine ⟨288295425069103518984595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384393900092138025312793 288295425069103518984595)
                  ·
                    rfl

theorem cell20_631635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2].length) (baseStart_631635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631635 prefixEnd_631635 := by exact prefixLift 631635
  have htrace : WordTrace (prefixWord ++ tailWord_631635) baseStart_631635 baseEnd_631635 := by
    simpa [prefixWord, tailWord_631635, baseEnd_631635] using wordTrace_append hprefix tailTrace_631635
  have hstable : (prefixWord ++ tailWord_631635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631635).length < 2 ^ (prefixWord ++ tailWord_631635).sum := by decide
  have hdescent : baseEnd_631635 < baseStart_631635 := by decide
  rcases family_descends (prefixWord ++ tailWord_631635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631642 : List Nat := [3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_631642 : Nat := 118140960795 + 631642 * 2 ^ 59
def prefixEnd_631642 : Nat := 4983230072969 + 3 ^ 40 * 631642 * 2
def baseEnd_631642 : Nat := 96099540019947535250411

theorem tailTrace_631642 : CollatzResearch.WordTrace tailWord_631642 prefixEnd_631642 96099540019947535250411 := by
  unfold tailWord_631642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759469094419096177568295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15358584251784256473515453 5759469094419096177568295)
  ·
    refine ⟨8639203641628644266352443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5759469094419096177568295 8639203641628644266352443)
    ·
      refine ⟨12958805462442966399528665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639203641628644266352443 12958805462442966399528665)
      ·
        refine ⟨9719104096832224799646499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12958805462442966399528665 9719104096832224799646499)
        ·
          refine ⟨14578656145248337199469749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9719104096832224799646499 14578656145248337199469749)
          ·
            refine ⟨1366749013617031612450289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14578656145248337199469749 1366749013617031612450289)
            ·
              refine ⟨1025061760212773709337717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366749013617031612450289 1025061760212773709337717)
              ·
                refine ⟨96099540019947535250411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025061760212773709337717 96099540019947535250411)
                ·
                  rfl

theorem cell20_631642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_631642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631642 prefixEnd_631642 := by exact prefixLift 631642
  have htrace : WordTrace (prefixWord ++ tailWord_631642) baseStart_631642 baseEnd_631642 := by
    simpa [prefixWord, tailWord_631642, baseEnd_631642] using wordTrace_append hprefix tailTrace_631642
  have hstable : (prefixWord ++ tailWord_631642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631642).length < 2 ^ (prefixWord ++ tailWord_631642).sum := by decide
  have hdescent : baseEnd_631642 < baseStart_631642 := by decide
  rcases family_descends (prefixWord ++ tailWord_631642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631682 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_631682 : Nat := 118140960795 + 631682 * 2 ^ 59
def prefixEnd_631682 : Nat := 4983230072969 + 3 ^ 40 * 631682 * 2
def baseEnd_631682 : Nat := 288316877149780244417737

theorem tailTrace_631682 : CollatzResearch.WordTrace tailWord_631682 prefixEnd_631682 288316877149780244417737 := by
  unfold tailWord_631682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759833824382867885432325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15359556865020981027819533 5759833824382867885432325)
  ·
    refine ⟨1079968842071787728518561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5759833824382867885432325 1079968842071787728518561)
    ·
      refine ⟨809976631553840796388921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079968842071787728518561 809976631553840796388921)
      ·
        refine ⟨607482473665380597291691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809976631553840796388921 607482473665380597291691)
        ·
          refine ⟨911223710498070895937537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607482473665380597291691 911223710498070895937537)
          ·
            refine ⟨683417782873553171953153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911223710498070895937537 683417782873553171953153)
            ·
              refine ⟨512563337155164878964865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683417782873553171953153 512563337155164878964865)
              ·
                refine ⟨384422502866373659223649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512563337155164878964865 384422502866373659223649)
                ·
                  refine ⟨288316877149780244417737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384422502866373659223649 288316877149780244417737)
                  ·
                    rfl

theorem cell20_631682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_631682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631682 prefixEnd_631682 := by exact prefixLift 631682
  have htrace : WordTrace (prefixWord ++ tailWord_631682) baseStart_631682 baseEnd_631682 := by
    simpa [prefixWord, tailWord_631682, baseEnd_631682] using wordTrace_append hprefix tailTrace_631682
  have hstable : (prefixWord ++ tailWord_631682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631682).length < 2 ^ (prefixWord ++ tailWord_631682).sum := by decide
  have hdescent : baseEnd_631682 < baseStart_631682 := by decide
  rcases family_descends (prefixWord ++ tailWord_631682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631711 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_631711 : Nat := 118140960795 + 631711 * 2 ^ 59
def prefixEnd_631711 : Nat := 4983230072969 + 3 ^ 40 * 631711 * 2
def baseEnd_631711 : Nat := 288330113539985032450951

theorem tailTrace_631711 : CollatzResearch.WordTrace tailWord_631711 prefixEnd_631711 288330113539985032450951 := by
  unfold tailWord_631711
  simp only [CollatzResearch.WordTrace]
  refine ⟨23040393014426409494534987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15360262009617606329689991 23040393014426409494534987)
  ·
    refine ⟨34560589521639614241802481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23040393014426409494534987 34560589521639614241802481)
    ·
      refine ⟨25920442141229710681351861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34560589521639614241802481 25920442141229710681351861)
      ·
        refine ⟨2430041450740285376376737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25920442141229710681351861 2430041450740285376376737)
        ·
          refine ⟨1822531088055214032282553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430041450740285376376737 1822531088055214032282553)
          ·
            refine ⟨1366898316041410524211915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822531088055214032282553 1366898316041410524211915)
            ·
              refine ⟨2050347474062115786317873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366898316041410524211915 2050347474062115786317873)
              ·
                refine ⟨1537760605546586839738405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050347474062115786317873 1537760605546586839738405)
                ·
                  refine ⟨288330113539985032450951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537760605546586839738405 288330113539985032450951)
                  ·
                    rfl

theorem cell20_631711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_631711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631711 prefixEnd_631711 := by exact prefixLift 631711
  have htrace : WordTrace (prefixWord ++ tailWord_631711) baseStart_631711 baseEnd_631711 := by
    simpa [prefixWord, tailWord_631711, baseEnd_631711] using wordTrace_append hprefix tailTrace_631711
  have hstable : (prefixWord ++ tailWord_631711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631711).length < 2 ^ (prefixWord ++ tailWord_631711).sum := by decide
  have hdescent : baseEnd_631711 < baseStart_631711 := by decide
  rcases family_descends (prefixWord ++ tailWord_631711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631734 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_631734 : Nat := 118140960795 + 631734 * 2 ^ 59
def prefixEnd_631734 : Nat := 4983230072969 + 3 ^ 40 * 631734 * 2
def baseEnd_631734 : Nat := 288340611366699174684191

theorem tailTrace_631734 : CollatzResearch.WordTrace tailWord_631734 prefixEnd_631734 288340611366699174684191 := by
  unfold tailWord_631734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440076993333942776413891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15360821262228722948414837 1440076993333942776413891)
  ·
    refine ⟨2160115490000914164620837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1440076993333942776413891 2160115490000914164620837)
    ·
      refine ⟨405021654375171405866407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2160115490000914164620837 405021654375171405866407)
      ·
        refine ⟨607532481562757108799611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405021654375171405866407 607532481562757108799611)
        ·
          refine ⟨911298722344135663199417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607532481562757108799611 911298722344135663199417)
          ·
            refine ⟨683474041758101747399563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911298722344135663199417 683474041758101747399563)
            ·
              refine ⟨1025211062637152621099345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683474041758101747399563 1025211062637152621099345)
              ·
                refine ⟨768908296977864465824509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025211062637152621099345 768908296977864465824509)
                ·
                  refine ⟨288340611366699174684191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768908296977864465824509 288340611366699174684191)
                  ·
                    rfl

theorem cell20_631734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_631734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631734 prefixEnd_631734 := by exact prefixLift 631734
  have htrace : WordTrace (prefixWord ++ tailWord_631734) baseStart_631734 baseEnd_631734 := by
    simpa [prefixWord, tailWord_631734, baseEnd_631734] using wordTrace_append hprefix tailTrace_631734
  have hstable : (prefixWord ++ tailWord_631734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631734).length < 2 ^ (prefixWord ++ tailWord_631734).sum := by decide
  have hdescent : baseEnd_631734 < baseStart_631734 := by decide
  rcases family_descends (prefixWord ++ tailWord_631734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631766 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_631766 : Nat := 118140960795 + 631766 * 2 ^ 59
def prefixEnd_631766 : Nat := 4983230072969 + 3 ^ 40 * 631766 * 2
def baseEnd_631766 : Nat := 288355217038649285617393

theorem tailTrace_631766 : CollatzResearch.WordTrace tailWord_631766 prefixEnd_631766 288355217038649285617393 := by
  unfold tailWord_631766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440149939326697117986697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15361599352818102591858101 1440149939326697117986697)
  ·
    refine ⟨1080112454495022838490023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1440149939326697117986697 1080112454495022838490023)
    ·
      refine ⟨1620168681742534257735035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080112454495022838490023 1620168681742534257735035)
      ·
        refine ⟨2430253022613801386602553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620168681742534257735035 2430253022613801386602553)
        ·
          refine ⟨1822689766960351039951915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430253022613801386602553 1822689766960351039951915)
          ·
            refine ⟨2734034650440526559927873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822689766960351039951915 2734034650440526559927873)
            ·
              refine ⟨2050525987830394919945905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734034650440526559927873 2050525987830394919945905)
              ·
                refine ⟨1537894490872796189959429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050525987830394919945905 1537894490872796189959429)
                ·
                  refine ⟨288355217038649285617393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537894490872796189959429 288355217038649285617393)
                  ·
                    rfl

theorem cell20_631766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_631766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631766 prefixEnd_631766 := by exact prefixLift 631766
  have htrace : WordTrace (prefixWord ++ tailWord_631766) baseStart_631766 baseEnd_631766 := by
    simpa [prefixWord, tailWord_631766, baseEnd_631766] using wordTrace_append hprefix tailTrace_631766
  have hstable : (prefixWord ++ tailWord_631766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631766).length < 2 ^ (prefixWord ++ tailWord_631766).sum := by decide
  have hdescent : baseEnd_631766 < baseStart_631766 := by decide
  rcases family_descends (prefixWord ++ tailWord_631766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631773 : List Nat := [1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_631773 : Nat := 118140960795 + 631773 * 2 ^ 59
def prefixEnd_631773 : Nat := 4983230072969 + 3 ^ 40 * 631773 * 2
def baseEnd_631773 : Nat := 96119470676462790794677

theorem tailTrace_631773 : CollatzResearch.WordTrace tailWord_631773 prefixEnd_631773 96119470676462790794677 := by
  unfold tailWord_631773
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042654340201794083291973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15361769560134529388861315 23042654340201794083291973)
  ·
    refine ⟨4320497688787836390617245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23042654340201794083291973 4320497688787836390617245)
    ·
      refine ⟨1620186633295438646481467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4320497688787836390617245 1620186633295438646481467)
      ·
        refine ⟨2430279949943157969722201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620186633295438646481467 2430279949943157969722201)
        ·
          refine ⟨1822709962457368477291651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430279949943157969722201 1822709962457368477291651)
          ·
            refine ⟨2734064943686052715937477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822709962457368477291651 2734064943686052715937477)
            ·
              refine ⟨512637176941134884238277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2734064943686052715937477 512637176941134884238277)
              ·
                refine ⟨96119470676462790794677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512637176941134884238277 96119470676462790794677)
                ·
                  rfl

theorem cell20_631773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_631773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631773 prefixEnd_631773 := by exact prefixLift 631773
  have htrace : WordTrace (prefixWord ++ tailWord_631773) baseStart_631773 baseEnd_631773 := by
    simpa [prefixWord, tailWord_631773, baseEnd_631773] using wordTrace_append hprefix tailTrace_631773
  have hstable : (prefixWord ++ tailWord_631773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631773).length < 2 ^ (prefixWord ++ tailWord_631773).sum := by decide
  have hdescent : baseEnd_631773 < baseStart_631773 := by decide
  rcases family_descends (prefixWord ++ tailWord_631773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631783 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 2]
def baseStart_631783 : Nat := 118140960795 + 631783 * 2 ^ 59
def prefixEnd_631783 : Nat := 4983230072969 + 3 ^ 40 * 631783 * 2
def baseEnd_631783 : Nat := 288362976301872782050657

theorem tailTrace_631783 : CollatzResearch.WordTrace tailWord_631783 prefixEnd_631783 288362976301872782050657 := by
  unfold tailWord_631783
  simp only [CollatzResearch.WordTrace]
  refine ⟨23043019070165565791156003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15362012713443710527437335 23043019070165565791156003)
  ·
    refine ⟨34564528605248348686734005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23043019070165565791156003 34564528605248348686734005)
    ·
      refine ⟨3240424556742032689381313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34564528605248348686734005 3240424556742032689381313)
      ·
        refine ⟨2430318417556524517035985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3240424556742032689381313 2430318417556524517035985)
        ·
          refine ⟨1822738813167393387776989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430318417556524517035985 1822738813167393387776989)
          ·
            refine ⟨683527054937772520416371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1822738813167393387776989 683527054937772520416371)
            ·
              refine ⟨1025290582406658780624557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683527054937772520416371 1025290582406658780624557)
              ·
                refine ⟨384483968402497042734209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1025290582406658780624557 384483968402497042734209)
                ·
                  refine ⟨288362976301872782050657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384483968402497042734209 288362976301872782050657)
                  ·
                    rfl

theorem cell20_631783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2].length) (baseStart_631783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631783 prefixEnd_631783 := by exact prefixLift 631783
  have htrace : WordTrace (prefixWord ++ tailWord_631783) baseStart_631783 baseEnd_631783 := by
    simpa [prefixWord, tailWord_631783, baseEnd_631783] using wordTrace_append hprefix tailTrace_631783
  have hstable : (prefixWord ++ tailWord_631783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631783).length < 2 ^ (prefixWord ++ tailWord_631783).sum := by decide
  have hdescent : baseEnd_631783 < baseStart_631783 := by decide
  rcases family_descends (prefixWord ++ tailWord_631783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631796 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_631796 : Nat := 118140960795 + 631796 * 2 ^ 59
def prefixEnd_631796 : Nat := 4983230072969 + 3 ^ 40 * 631796 * 2
def baseEnd_631796 : Nat := 288368909856102514617271

theorem tailTrace_631796 : CollatzResearch.WordTrace tailWord_631796 prefixEnd_631796 288368909856102514617271 := by
  unfold tailWord_631796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11521746609559234505689621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15362328812745646007586161 11521746609559234505689621)
  ·
    refine ⟨540081872323089117454201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11521746609559234505689621 540081872323089117454201)
    ·
      refine ⟨405061404242316838090651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540081872323089117454201 405061404242316838090651)
      ·
        refine ⟨607592106363475257135977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405061404242316838090651 607592106363475257135977)
        ·
          refine ⟨455694079772606442851983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607592106363475257135977 455694079772606442851983)
          ·
            refine ⟨683541119658909664277975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455694079772606442851983 683541119658909664277975)
            ·
              refine ⟨1025311679488364496416963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683541119658909664277975 1025311679488364496416963)
              ·
                refine ⟨1537967519232546744625445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025311679488364496416963 1537967519232546744625445)
                ·
                  refine ⟨288368909856102514617271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537967519232546744625445 288368909856102514617271)
                  ·
                    rfl

theorem cell20_631796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_631796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631796 prefixEnd_631796 := by exact prefixLift 631796
  have htrace : WordTrace (prefixWord ++ tailWord_631796) baseStart_631796 baseEnd_631796 := by
    simpa [prefixWord, tailWord_631796, baseEnd_631796] using wordTrace_append hprefix tailTrace_631796
  have hstable : (prefixWord ++ tailWord_631796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631796).length < 2 ^ (prefixWord ++ tailWord_631796).sum := by decide
  have hdescent : baseEnd_631796 < baseStart_631796 := by decide
  rcases family_descends (prefixWord ++ tailWord_631796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631801 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_631801 : Nat := 118140960795 + 631801 * 2 ^ 59
def prefixEnd_631801 : Nat := 4983230072969 + 3 ^ 40 * 631801 * 2
def baseEnd_631801 : Nat := 288371191992344719450583

theorem tailTrace_631801 : CollatzResearch.WordTrace tailWord_631801 prefixEnd_631801 288371191992344719450583 := by
  unfold tailWord_631801
  simp only [CollatzResearch.WordTrace]
  refine ⟨23043675584100354865311257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15362450389400236576874171 23043675584100354865311257)
  ·
    refine ⟨17282756688075266148983443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23043675584100354865311257 17282756688075266148983443)
    ·
      refine ⟨25924135032112899223475165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17282756688075266148983443 25924135032112899223475165)
      ·
        refine ⟨9721550637042337208803187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25924135032112899223475165 9721550637042337208803187)
        ·
          refine ⟨14582325955563505813204781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9721550637042337208803187 14582325955563505813204781)
          ·
            refine ⟨5468372233336314679951793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14582325955563505813204781 5468372233336314679951793)
            ·
              refine ⟨4101279175002236009963845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468372233336314679951793 4101279175002236009963845)
              ·
                refine ⟨768989845312919251868221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4101279175002236009963845 768989845312919251868221)
                ·
                  refine ⟨288371191992344719450583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768989845312919251868221 288371191992344719450583)
                  ·
                    rfl

theorem cell20_631801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_631801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631801 prefixEnd_631801 := by exact prefixLift 631801
  have htrace : WordTrace (prefixWord ++ tailWord_631801) baseStart_631801 baseEnd_631801 := by
    simpa [prefixWord, tailWord_631801, baseEnd_631801] using wordTrace_append hprefix tailTrace_631801
  have hstable : (prefixWord ++ tailWord_631801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631801).length < 2 ^ (prefixWord ++ tailWord_631801).sum := by decide
  have hdescent : baseEnd_631801 < baseStart_631801 := by decide
  rcases family_descends (prefixWord ++ tailWord_631801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631810 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_631810 : Nat := 118140960795 + 631810 * 2 ^ 59
def prefixEnd_631810 : Nat := 4983230072969 + 3 ^ 40 * 631810 * 2
def baseEnd_631810 : Nat := 288375299837580688150547

theorem tailTrace_631810 : CollatzResearch.WordTrace tailWord_631810 prefixEnd_631810 288375299837580688150547 := by
  unfold tailWord_631810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761000960266937350597221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15362669227378499601592589 5761000960266937350597221)
  ·
    refine ⟨1080187680050050753236979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5761000960266937350597221 1080187680050050753236979)
    ·
      refine ⟨1620281520075076129855469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080187680050050753236979 1620281520075076129855469)
      ·
        refine ⟨607605570028153548695801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1620281520075076129855469 607605570028153548695801)
        ·
          refine ⟨455704177521115161521851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607605570028153548695801 455704177521115161521851)
          ·
            refine ⟨683556266281672742282777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455704177521115161521851 683556266281672742282777)
            ·
              refine ⟨512667199711254556712083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683556266281672742282777 512667199711254556712083)
              ·
                refine ⟨769000799566881835068125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512667199711254556712083 769000799566881835068125)
                ·
                  refine ⟨288375299837580688150547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769000799566881835068125 288375299837580688150547)
                  ·
                    rfl

theorem cell20_631810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_631810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631810 prefixEnd_631810 := by exact prefixLift 631810
  have htrace : WordTrace (prefixWord ++ tailWord_631810) baseStart_631810 baseEnd_631810 := by
    simpa [prefixWord, tailWord_631810, baseEnd_631810] using wordTrace_append hprefix tailTrace_631810
  have hstable : (prefixWord ++ tailWord_631810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631810).length < 2 ^ (prefixWord ++ tailWord_631810).sum := by decide
  have hdescent : baseEnd_631810 < baseStart_631810 := by decide
  rcases family_descends (prefixWord ++ tailWord_631810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631818 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_631818 : Nat := 118140960795 + 631818 * 2 ^ 59
def prefixEnd_631818 : Nat := 4983230072969 + 3 ^ 40 * 631818 * 2
def baseEnd_631818 : Nat := 288378951255568215883847

theorem tailTrace_631818 : CollatzResearch.WordTrace tailWord_631818 prefixEnd_631818 288378951255568215883847 := by
  unfold tailWord_631818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761073906259691692170027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15362863750025844512453405 5761073906259691692170027)
  ·
    refine ⟨8641610859389537538255041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5761073906259691692170027 8641610859389537538255041)
    ·
      refine ⟨6481208144542153153691281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8641610859389537538255041 6481208144542153153691281)
      ·
        refine ⟨4860906108406614865268461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481208144542153153691281 4860906108406614865268461)
        ·
          refine ⟨1822839790652480574475673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4860906108406614865268461 1822839790652480574475673)
          ·
            refine ⟨1367129842989360430856755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822839790652480574475673 1367129842989360430856755)
            ·
              refine ⟨2050694764484040646285133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367129842989360430856755 2050694764484040646285133)
              ·
                refine ⟨769010536681515242356925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2050694764484040646285133 769010536681515242356925)
                ·
                  refine ⟨288378951255568215883847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769010536681515242356925 288378951255568215883847)
                  ·
                    rfl

theorem cell20_631818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_631818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631818 prefixEnd_631818 := by exact prefixLift 631818
  have htrace : WordTrace (prefixWord ++ tailWord_631818) baseStart_631818 baseEnd_631818 := by
    simpa [prefixWord, tailWord_631818, baseEnd_631818] using wordTrace_append hprefix tailTrace_631818
  have hstable : (prefixWord ++ tailWord_631818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631818).length < 2 ^ (prefixWord ++ tailWord_631818).sum := by decide
  have hdescent : baseEnd_631818 < baseStart_631818 := by decide
  rcases family_descends (prefixWord ++ tailWord_631818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631877 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_631877 : Nat := 118140960795 + 631877 * 2 ^ 59
def prefixEnd_631877 : Nat := 4983230072969 + 3 ^ 40 * 631877 * 2
def baseEnd_631877 : Nat := 288405880463226232916939

theorem tailTrace_631877 : CollatzResearch.WordTrace tailWord_631877 prefixEnd_631877 288405880463226232916939 := by
  unfold tailWord_631877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23046447531825019845077885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15364298354550013230051923 23046447531825019845077885)
  ·
    refine ⟨8642417824434382441904207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23046447531825019845077885 8642417824434382441904207)
    ·
      refine ⟨12963626736651573662856311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8642417824434382441904207 12963626736651573662856311)
      ·
        refine ⟨19445440104977360494284467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12963626736651573662856311 19445440104977360494284467)
        ·
          refine ⟨29168160157466040741426701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19445440104977360494284467 29168160157466040741426701)
          ·
            refine ⟨10938060059049765278035013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29168160157466040741426701 10938060059049765278035013)
            ·
              refine ⟨2050886261071830989631565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10938060059049765278035013 2050886261071830989631565)
              ·
                refine ⟨769082347901936621111837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2050886261071830989631565 769082347901936621111837)
                ·
                  refine ⟨288405880463226232916939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769082347901936621111837 288405880463226232916939)
                  ·
                    rfl

theorem cell20_631877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_631877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631877 prefixEnd_631877 := by exact prefixLift 631877
  have htrace : WordTrace (prefixWord ++ tailWord_631877) baseStart_631877 baseEnd_631877 := by
    simpa [prefixWord, tailWord_631877, baseEnd_631877] using wordTrace_append hprefix tailTrace_631877
  have hstable : (prefixWord ++ tailWord_631877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631877).length < 2 ^ (prefixWord ++ tailWord_631877).sum := by decide
  have hdescent : baseEnd_631877 < baseStart_631877 := by decide
  rcases family_descends (prefixWord ++ tailWord_631877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631918 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_631918 : Nat := 118140960795 + 631918 * 2 ^ 59
def prefixEnd_631918 : Nat := 4983230072969 + 3 ^ 40 * 631918 * 2
def baseEnd_631918 : Nat := 288424593980412312550105

theorem tailTrace_631918 : CollatzResearch.WordTrace tailWord_631918 prefixEnd_631918 288424593980412312550105 := by
  unfold tailWord_631918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880992865584560480915051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15365295283117655898213605 2880992865584560480915051)
  ·
    refine ⟨4321489298376840721372577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2880992865584560480915051 4321489298376840721372577)
    ·
      refine ⟨3241116973782630541029433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4321489298376840721372577 3241116973782630541029433)
      ·
        refine ⟨2430837730336972905772075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3241116973782630541029433 2430837730336972905772075)
        ·
          refine ⟨3646256595505459358658113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430837730336972905772075 3646256595505459358658113)
          ·
            refine ⟨2734692446629094518993585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3646256595505459358658113 2734692446629094518993585)
            ·
              refine ⟨2051019334971820889245189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734692446629094518993585 2051019334971820889245189)
              ·
                refine ⟨384566125307216416733473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2051019334971820889245189 384566125307216416733473)
                ·
                  refine ⟨288424593980412312550105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384566125307216416733473 288424593980412312550105)
                  ·
                    rfl

theorem cell20_631918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_631918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631918 prefixEnd_631918 := by exact prefixLift 631918
  have htrace : WordTrace (prefixWord ++ tailWord_631918) baseStart_631918 baseEnd_631918 := by
    simpa [prefixWord, tailWord_631918, baseEnd_631918] using wordTrace_append hprefix tailTrace_631918
  have hstable : (prefixWord ++ tailWord_631918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631918).length < 2 ^ (prefixWord ++ tailWord_631918).sum := by decide
  have hdescent : baseEnd_631918 < baseStart_631918 := by decide
  rcases family_descends (prefixWord ++ tailWord_631918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631932 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_631932 : Nat := 118140960795 + 631932 * 2 ^ 59
def prefixEnd_631932 : Nat := 4983230072969 + 3 ^ 40 * 631932 * 2
def baseEnd_631932 : Nat := 288430983961890486083381

theorem tailTrace_631932 : CollatzResearch.WordTrace tailWord_631932 prefixEnd_631932 288430983961890486083381 := by
  unfold tailWord_631932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524226773312882119165025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15365635697750509492220033 11524226773312882119165025)
  ·
    refine ⟨8643170079984661589373769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11524226773312882119165025 8643170079984661589373769)
    ·
      refine ⟨6482377559988496192030327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8643170079984661589373769 6482377559988496192030327)
      ·
        refine ⟨9723566339982744288045491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482377559988496192030327 9723566339982744288045491)
        ·
          refine ⟨14585349509974116432068237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723566339982744288045491 14585349509974116432068237)
          ·
            refine ⟨5469506066240293662025589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14585349509974116432068237 5469506066240293662025589)
            ·
              refine ⟨512766193710027530814899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5469506066240293662025589 512766193710027530814899)
              ·
                refine ⟨769149290565041296222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512766193710027530814899 769149290565041296222349)
                ·
                  refine ⟨288430983961890486083381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769149290565041296222349 288430983961890486083381)
                  ·
                    rfl

theorem cell20_631932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_631932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631932 prefixEnd_631932 := by exact prefixLift 631932
  have htrace : WordTrace (prefixWord ++ tailWord_631932) baseStart_631932 baseEnd_631932 := by
    simpa [prefixWord, tailWord_631932, baseEnd_631932] using wordTrace_append hprefix tailTrace_631932
  have hstable : (prefixWord ++ tailWord_631932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631932).length < 2 ^ (prefixWord ++ tailWord_631932).sum := by decide
  have hdescent : baseEnd_631932 < baseStart_631932 := by decide
  rcases family_descends (prefixWord ++ tailWord_631932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631991 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_631991 : Nat := 118140960795 + 631991 * 2 ^ 59
def prefixEnd_631991 : Nat := 4983230072969 + 3 ^ 40 * 631991 * 2
def baseEnd_631991 : Nat := 288457913169548503116473

theorem tailTrace_631991 : CollatzResearch.WordTrace tailWord_631991 prefixEnd_631991 288457913169548503116473 := by
  unfold tailWord_631991
  simp only [CollatzResearch.WordTrace]
  refine ⟨23050605453412017314727827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15367070302274678209818551 23050605453412017314727827)
  ·
    refine ⟨34575908180118025972091741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23050605453412017314727827 34575908180118025972091741)
    ·
      refine ⟨12965965567544259739534403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34575908180118025972091741 12965965567544259739534403)
      ·
        refine ⟨19448948351316389609301605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965965567544259739534403 19448948351316389609301605)
        ·
          refine ⟨3646677815871823051744051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19448948351316389609301605 3646677815871823051744051)
          ·
            refine ⟨5470016723807734577616077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646677815871823051744051 5470016723807734577616077)
            ·
              refine ⟨2051256271427900466606029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5470016723807734577616077 2051256271427900466606029)
              ·
                refine ⟨769221101785462674977261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2051256271427900466606029 769221101785462674977261)
                ·
                  refine ⟨288457913169548503116473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769221101785462674977261 288457913169548503116473)
                  ·
                    rfl

theorem cell20_631991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_631991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_631991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_631991 prefixEnd_631991 := by exact prefixLift 631991
  have htrace : WordTrace (prefixWord ++ tailWord_631991) baseStart_631991 baseEnd_631991 := by
    simpa [prefixWord, tailWord_631991, baseEnd_631991] using wordTrace_append hprefix tailTrace_631991
  have hstable : (prefixWord ++ tailWord_631991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631991).length < 2 ^ (prefixWord ++ tailWord_631991).sum := by decide
  have hdescent : baseEnd_631991 < baseStart_631991 := by decide
  rcases family_descends (prefixWord ++ tailWord_631991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632019 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_632019 : Nat := 118140960795 + 632019 * 2 ^ 59
def prefixEnd_632019 : Nat := 4983230072969 + 3 ^ 40 * 632019 * 2
def baseEnd_632019 : Nat := 288470693132504850183025

theorem tailTrace_632019 : CollatzResearch.WordTrace tailWord_632019 prefixEnd_632019 288470693132504850183025 := by
  unfold tailWord_632019
  simp only [CollatzResearch.WordTrace]
  refine ⟨23051626697310578096747111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15367751131540385397831407 23051626697310578096747111)
  ·
    refine ⟨34577440045965867145120667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23051626697310578096747111 34577440045965867145120667)
    ·
      refine ⟨51866160068948800717681001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34577440045965867145120667 51866160068948800717681001)
      ·
        refine ⟨38899620051711600538260751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51866160068948800717681001 38899620051711600538260751)
        ·
          refine ⟨58349430077567400807391127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38899620051711600538260751 58349430077567400807391127)
          ·
            refine ⟨87524145116351101211086691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58349430077567400807391127 87524145116351101211086691)
            ·
              refine ⟨131286217674526651816630037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87524145116351101211086691 131286217674526651816630037)
              ·
                refine ⟨6154041453493436803904533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131286217674526651816630037 6154041453493436803904533)
                ·
                  refine ⟨288470693132504850183025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6154041453493436803904533 288470693132504850183025)
                  ·
                    rfl

theorem cell20_632019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_632019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632019 prefixEnd_632019 := by exact prefixLift 632019
  have htrace : WordTrace (prefixWord ++ tailWord_632019) baseStart_632019 baseEnd_632019 := by
    simpa [prefixWord, tailWord_632019, baseEnd_632019] using wordTrace_append hprefix tailTrace_632019
  have hstable : (prefixWord ++ tailWord_632019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632019).length < 2 ^ (prefixWord ++ tailWord_632019).sum := by decide
  have hdescent : baseEnd_632019 < baseStart_632019 := by decide
  rcases family_descends (prefixWord ++ tailWord_632019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632022 : List Nat := [5, 2, 1, 2, 10]
def baseStart_632022 : Nat := 118140960795 + 632022 * 2 ^ 59
def prefixEnd_632022 : Nat := 4983230072969 + 3 ^ 40 * 632022 * 2
def baseEnd_632022 : Nat := 3561383486595681149173

theorem tailTrace_632022 : CollatzResearch.WordTrace tailWord_632022 prefixEnd_632022 3561383486595681149173 := by
  unfold tailWord_632022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440733507268731850569145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15367824077533139739404213 1440733507268731850569145)
  ·
    refine ⟨1080550130451548887926859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1440733507268731850569145 1080550130451548887926859)
    ·
      refine ⟨1620825195677323331890289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080550130451548887926859 1620825195677323331890289)
      ·
        refine ⟨1215618896757992498917717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620825195677323331890289 1215618896757992498917717)
        ·
          refine ⟨3561383486595681149173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1215618896757992498917717 3561383486595681149173)
          ·
            rfl

theorem cell20_632022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 10].length) (baseStart_632022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632022 prefixEnd_632022 := by exact prefixLift 632022
  have htrace : WordTrace (prefixWord ++ tailWord_632022) baseStart_632022 baseEnd_632022 := by
    simpa [prefixWord, tailWord_632022, baseEnd_632022] using wordTrace_append hprefix tailTrace_632022
  have hstable : (prefixWord ++ tailWord_632022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632022).length < 2 ^ (prefixWord ++ tailWord_632022).sum := by decide
  have hdescent : baseEnd_632022 < baseStart_632022 := by decide
  rcases family_descends (prefixWord ++ tailWord_632022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632032 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_632032 : Nat := 118140960795 + 632032 * 2 ^ 59
def prefixEnd_632032 : Nat := 4983230072969 + 3 ^ 40 * 632032 * 2
def baseEnd_632032 : Nat := 288476626686734582749639

theorem tailTrace_632032 : CollatzResearch.WordTrace tailWord_632032 prefixEnd_632032 288476626686734582749639 := by
  unfold tailWord_632032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11526050423131740658485175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15368067230842320877980233 11526050423131740658485175)
  ·
    refine ⟨17289075634697610987727763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11526050423131740658485175 17289075634697610987727763)
    ·
      refine ⟨25933613452046416481591645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17289075634697610987727763 25933613452046416481591645)
      ·
        refine ⟨9725105044517406180596867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25933613452046416481591645 9725105044517406180596867)
        ·
          refine ⟨14587657566776109270895301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9725105044517406180596867 14587657566776109270895301)
          ·
            refine ⟨2735185793770520488292869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14587657566776109270895301 2735185793770520488292869)
            ·
              refine ⟨512847336331972591554913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2735185793770520488292869 512847336331972591554913)
              ·
                refine ⟨384635502248979443666185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512847336331972591554913 384635502248979443666185)
                ·
                  refine ⟨288476626686734582749639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384635502248979443666185 288476626686734582749639)
                  ·
                    rfl

theorem cell20_632032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_632032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632032 prefixEnd_632032 := by exact prefixLift 632032
  have htrace : WordTrace (prefixWord ++ tailWord_632032) baseStart_632032 baseEnd_632032 := by
    simpa [prefixWord, tailWord_632032, baseEnd_632032] using wordTrace_append hprefix tailTrace_632032
  have hstable : (prefixWord ++ tailWord_632032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632032).length < 2 ^ (prefixWord ++ tailWord_632032).sum := by decide
  have hdescent : baseEnd_632032 < baseStart_632032 := by decide
  rcases family_descends (prefixWord ++ tailWord_632032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632039 : List Nat := [1, 1, 5, 3, 2, 2, 1, 5]
def baseStart_632039 : Nat := 118140960795 + 632039 * 2 ^ 59
def prefixEnd_632039 : Nat := 4983230072969 + 3 ^ 40 * 632039 * 2
def baseEnd_632039 : Nat := 96159940559157889838759

theorem tailTrace_632039 : CollatzResearch.WordTrace tailWord_632039 prefixEnd_632039 96159940559157889838759 := by
  unfold tailWord_632039
  simp only [CollatzResearch.WordTrace]
  refine ⟨23052356157238121512475171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15368237438158747674983447 23052356157238121512475171)
  ·
    refine ⟨34578534235857182268712757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23052356157238121512475171 34578534235857182268712757)
    ·
      refine ⟨3241737584611610837691821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34578534235857182268712757 3241737584611610837691821)
      ·
        refine ⟨1215651594229354064134433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3241737584611610837691821 1215651594229354064134433)
        ·
          refine ⟨911738695672015548100825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215651594229354064134433 911738695672015548100825)
          ·
            refine ⟨683804021754011661075619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911738695672015548100825 683804021754011661075619)
            ·
              refine ⟨1025706032631017491613429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683804021754011661075619 1025706032631017491613429)
              ·
                refine ⟨96159940559157889838759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025706032631017491613429 96159940559157889838759)
                ·
                  rfl

theorem cell20_632039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_632039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632039 prefixEnd_632039 := by exact prefixLift 632039
  have htrace : WordTrace (prefixWord ++ tailWord_632039) baseStart_632039 baseEnd_632039 := by
    simpa [prefixWord, tailWord_632039, baseEnd_632039] using wordTrace_append hprefix tailTrace_632039
  have hstable : (prefixWord ++ tailWord_632039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632039).length < 2 ^ (prefixWord ++ tailWord_632039).sum := by decide
  have hdescent : baseEnd_632039 < baseStart_632039 := by decide
  rcases family_descends (prefixWord ++ tailWord_632039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632043 : List Nat := [1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_632043 : Nat := 118140960795 + 632043 * 2 ^ 59
def prefixEnd_632043 : Nat := 4983230072969 + 3 ^ 40 * 632043 * 2
def baseEnd_632043 : Nat := 96160549128822477794309

theorem tailTrace_632043 : CollatzResearch.WordTrace tailWord_632043 prefixEnd_632043 96160549128822477794309 := by
  unfold tailWord_632043
  simp only [CollatzResearch.WordTrace]
  refine ⟨23052502049223630195620783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15368334699482420130413855 23052502049223630195620783)
  ·
    refine ⟨34578753073835445293431175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23052502049223630195620783 34578753073835445293431175)
    ·
      refine ⟨51868129610753167940146763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34578753073835445293431175 51868129610753167940146763)
      ·
        refine ⟨77802194416129751910220145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51868129610753167940146763 77802194416129751910220145)
        ·
          refine ⟨58351645812097313932665109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77802194416129751910220145 58351645812097313932665109)
          ·
            refine ⟨2735233397442061590593677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58351645812097313932665109 2735233397442061590593677)
            ·
              refine ⟨1025712524040773096472629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2735233397442061590593677 1025712524040773096472629)
              ·
                refine ⟨96160549128822477794309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025712524040773096472629 96160549128822477794309)
                ·
                  rfl

theorem cell20_632043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_632043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632043 prefixEnd_632043 := by exact prefixLift 632043
  have htrace : WordTrace (prefixWord ++ tailWord_632043) baseStart_632043 baseEnd_632043 := by
    simpa [prefixWord, tailWord_632043, baseEnd_632043] using wordTrace_append hprefix tailTrace_632043
  have hstable : (prefixWord ++ tailWord_632043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632043).length < 2 ^ (prefixWord ++ tailWord_632043).sum := by decide
  have hdescent : baseEnd_632043 < baseStart_632043 := by decide
  rcases family_descends (prefixWord ++ tailWord_632043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632133 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_632133 : Nat := 118140960795 + 632133 * 2 ^ 59
def prefixEnd_632133 : Nat := 4983230072969 + 3 ^ 40 * 632133 * 2
def baseEnd_632133 : Nat := 288522725838827120382559

theorem tailTrace_632133 : CollatzResearch.WordTrace tailWord_632133 prefixEnd_632133 288522725838827120382559 := by
  unfold tailWord_632133
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055784618897575566397053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15370523079265050377598035 23055784618897575566397053)
  ·
    refine ⟨8645919232086590837398895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23055784618897575566397053 8645919232086590837398895)
    ·
      refine ⟨12968878848129886256098343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8645919232086590837398895 12968878848129886256098343)
      ·
        refine ⟨19453318272194829384147515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12968878848129886256098343 19453318272194829384147515)
        ·
          refine ⟨29179977408292244076221273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19453318272194829384147515 29179977408292244076221273)
          ·
            refine ⟨21884983056219183057165955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29179977408292244076221273 21884983056219183057165955)
            ·
              refine ⟨32827474584328774585748933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21884983056219183057165955 32827474584328774585748933)
              ·
                refine ⟨6155151484561645234827925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32827474584328774585748933 6155151484561645234827925)
                ·
                  refine ⟨288522725838827120382559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6155151484561645234827925 288522725838827120382559)
                  ·
                    rfl

theorem cell20_632133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_632133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632133 prefixEnd_632133 := by exact prefixLift 632133
  have htrace : WordTrace (prefixWord ++ tailWord_632133) baseStart_632133 baseEnd_632133 := by
    simpa [prefixWord, tailWord_632133, baseEnd_632133] using wordTrace_append hprefix tailTrace_632133
  have hstable : (prefixWord ++ tailWord_632133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632133).length < 2 ^ (prefixWord ++ tailWord_632133).sum := by decide
  have hdescent : baseEnd_632133 < baseStart_632133 := by decide
  rcases family_descends (prefixWord ++ tailWord_632133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632160 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_632160 : Nat := 118140960795 + 632160 * 2 ^ 59
def prefixEnd_632160 : Nat := 4983230072969 + 3 ^ 40 * 632160 * 2
def baseEnd_632160 : Nat := 288535049374535026482449

theorem tailTrace_632160 : CollatzResearch.WordTrace tailWord_632160 prefixEnd_632160 288535049374535026482449 := by
  unfold tailWord_632160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11528384694899879588814967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15371179593199839451753289 11528384694899879588814967)
  ·
    refine ⟨17292577042349819383222451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11528384694899879588814967 17292577042349819383222451)
    ·
      refine ⟨25938865563524729074833677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17292577042349819383222451 25938865563524729074833677)
      ·
        refine ⟨9727074586321773403062629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25938865563524729074833677 9727074586321773403062629)
        ·
          refine ⟨1823826484935332513074243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9727074586321773403062629 1823826484935332513074243)
          ·
            refine ⟨2735739727402998769611365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823826484935332513074243 2735739727402998769611365)
            ·
              refine ⟨512951198888062269302131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2735739727402998769611365 512951198888062269302131)
              ·
                refine ⟨769426798332093403953197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512951198888062269302131 769426798332093403953197)
                ·
                  refine ⟨288535049374535026482449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769426798332093403953197 288535049374535026482449)
                  ·
                    rfl

theorem cell20_632160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_632160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632160 prefixEnd_632160 := by exact prefixLift 632160
  have htrace : WordTrace (prefixWord ++ tailWord_632160) baseStart_632160 baseEnd_632160 := by
    simpa [prefixWord, tailWord_632160, baseEnd_632160] using wordTrace_append hprefix tailTrace_632160
  have hstable : (prefixWord ++ tailWord_632160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632160).length < 2 ^ (prefixWord ++ tailWord_632160).sum := by decide
  have hdescent : baseEnd_632160 < baseStart_632160 := by decide
  rcases family_descends (prefixWord ++ tailWord_632160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632201 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 2]
def baseStart_632201 : Nat := 118140960795 + 632201 * 2 ^ 59
def prefixEnd_632201 : Nat := 4983230072969 + 3 ^ 40 * 632201 * 2
def baseEnd_632201 : Nat := 288553762891721106115615

theorem tailTrace_632201 : CollatzResearch.WordTrace tailWord_632201 prefixEnd_632201 288553762891721106115615 := by
  unfold tailWord_632201
  simp only [CollatzResearch.WordTrace]
  refine ⟨23058264782651223179872457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15372176521767482119914971 23058264782651223179872457)
  ·
    refine ⟨17293698586988417384904343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23058264782651223179872457 17293698586988417384904343)
    ·
      refine ⟨25940547880482626077356515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17293698586988417384904343 25940547880482626077356515)
      ·
        refine ⟨38910821820723939116034773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25940547880482626077356515 38910821820723939116034773)
        ·
          refine ⟨911972386423217323032065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38910821820723939116034773 911972386423217323032065)
          ·
            refine ⟨683979289817412992274049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911972386423217323032065 683979289817412992274049)
            ·
              refine ⟨512984467363059744205537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683979289817412992274049 512984467363059744205537)
              ·
                refine ⟨384738350522294808154153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512984467363059744205537 384738350522294808154153)
                ·
                  refine ⟨288553762891721106115615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384738350522294808154153 288553762891721106115615)
                  ·
                    rfl

theorem cell20_632201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_632201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632201 prefixEnd_632201 := by exact prefixLift 632201
  have htrace : WordTrace (prefixWord ++ tailWord_632201) baseStart_632201 baseEnd_632201 := by
    simpa [prefixWord, tailWord_632201, baseEnd_632201] using wordTrace_append hprefix tailTrace_632201
  have hstable : (prefixWord ++ tailWord_632201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632201).length < 2 ^ (prefixWord ++ tailWord_632201).sum := by decide
  have hdescent : baseEnd_632201 < baseStart_632201 := by decide
  rcases family_descends (prefixWord ++ tailWord_632201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632212 : List Nat := [2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_632212 : Nat := 118140960795 + 632212 * 2 ^ 59
def prefixEnd_632212 : Nat := 4983230072969 + 3 ^ 40 * 632212 * 2
def baseEnd_632212 : Nat := 96186261197151318916301

theorem tailTrace_632212 : CollatzResearch.WordTrace tailWord_632212 prefixEnd_632212 96186261197151318916301 := by
  unfold tailWord_632212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11529332992805686029261445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15372443990407581372348593 11529332992805686029261445)
  ·
    refine ⟨2161749936151066130486521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11529332992805686029261445 2161749936151066130486521)
    ·
      refine ⟨1621312452113299597864891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2161749936151066130486521 1621312452113299597864891)
      ·
        refine ⟨2431968678169949396797337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621312452113299597864891 2431968678169949396797337)
        ·
          refine ⟨1823976508627462047598003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2431968678169949396797337 1823976508627462047598003)
          ·
            refine ⟨2735964762941193071397005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823976508627462047598003 2735964762941193071397005)
            ·
              refine ⟨1025986786102947401773877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2735964762941193071397005 1025986786102947401773877)
              ·
                refine ⟨96186261197151318916301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025986786102947401773877 96186261197151318916301)
                ·
                  rfl

theorem cell20_632212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_632212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_632212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_632212 prefixEnd_632212 := by exact prefixLift 632212
  have htrace : WordTrace (prefixWord ++ tailWord_632212) baseStart_632212 baseEnd_632212 := by
    simpa [prefixWord, tailWord_632212, baseEnd_632212] using wordTrace_append hprefix tailTrace_632212
  have hstable : (prefixWord ++ tailWord_632212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632212).length < 2 ^ (prefixWord ++ tailWord_632212).sum := by decide
  have hdescent : baseEnd_632212 < baseStart_632212 := by decide
  rcases family_descends (prefixWord ++ tailWord_632212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
