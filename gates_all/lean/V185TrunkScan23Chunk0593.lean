import V185TrunkScan23Chunk0592

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3506288 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4]
def baseStart_3506288 : Nat := 118140960795 + 3506288 * 2 ^ 59
def prefixEnd_3506288 : Nat := 4983230072969 + 3 ^ 40 * 3506288 * 2
def baseEnd_3506288 : Nat := 1800411057091882865774881

theorem tailTrace_3506288 : CollatzResearch.WordTrace tailWord_3506288 prefixEnd_3506288 1800411057091882865774881 := by
  unfold tailWord_3506288
  simp only [CollatzResearch.WordTrace]
  refine ⟨63942414760662438580255759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85256553014216584773674345 63942414760662438580255759)
  ·
    refine ⟨95913622140993657870383639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63942414760662438580255759 95913622140993657870383639)
    ·
      refine ⟨143870433211490486805575459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95913622140993657870383639 143870433211490486805575459)
      ·
        refine ⟨215805649817235730208363189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143870433211490486805575459 215805649817235730208363189)
        ·
          refine ⟨20231779670365849707034049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215805649817235730208363189 20231779670365849707034049)
          ·
            refine ⟨15173834752774387280275537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231779670365849707034049 15173834752774387280275537)
            ·
              refine ⟨11380376064580790460206653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15173834752774387280275537 11380376064580790460206653)
              ·
                refine ⟨4267641024217796422577495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11380376064580790460206653 4267641024217796422577495)
                ·
                  refine ⟨6401461536326694633866243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267641024217796422577495 6401461536326694633866243)
                  ·
                    refine ⟨9602192304490041950799365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6401461536326694633866243 9602192304490041950799365)
                    ·
                      refine ⟨1800411057091882865774881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9602192304490041950799365 1800411057091882865774881)
                      ·
                        rfl

theorem cell23_3506288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 4].length) (baseStart_3506288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506288 prefixEnd_3506288 := by exact prefixLift 3506288
  have htrace : WordTrace (prefixWord ++ tailWord_3506288) baseStart_3506288 baseEnd_3506288 := by
    simpa [prefixWord, tailWord_3506288, baseEnd_3506288] using wordTrace_append hprefix tailTrace_3506288
  have hstable : (prefixWord ++ tailWord_3506288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506288).length < 2 ^ (prefixWord ++ tailWord_3506288).sum := by decide
  have hdescent : baseEnd_3506288 < baseStart_3506288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506301 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3506301 : Nat := 118140960795 + 3506301 * 2 ^ 59
def prefixEnd_3506301 : Nat := 4983230072969 + 3 ^ 40 * 3506301 * 2
def baseEnd_3506301 : Nat := 1800417732340391314912321

theorem tailTrace_3506301 : CollatzResearch.WordTrace tailWord_3506301 prefixEnd_3506301 1800417732340391314912321 := by
  unfold tailWord_3506301
  simp only [CollatzResearch.WordTrace]
  refine ⟨127885303670277780380734757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85256869113518520253823171 127885303670277780380734757)
  ·
    refine ⟨23978494438177083821387767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127885303670277780380734757 23978494438177083821387767)
    ·
      refine ⟨35967741657265625732081651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23978494438177083821387767 35967741657265625732081651)
      ·
        refine ⟨53951612485898438598122477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35967741657265625732081651 53951612485898438598122477)
        ·
          refine ⟨20231854682211914474295929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53951612485898438598122477 20231854682211914474295929)
          ·
            refine ⟨15173891011658935855721947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231854682211914474295929 15173891011658935855721947)
            ·
              refine ⟨22760836517488403783582921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173891011658935855721947 22760836517488403783582921)
              ·
                refine ⟨17070627388116302837687191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22760836517488403783582921 17070627388116302837687191)
                ·
                  refine ⟨25605941082174454256530787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17070627388116302837687191 25605941082174454256530787)
                  ·
                    refine ⟨38408911623261681384796181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25605941082174454256530787 38408911623261681384796181)
                    ·
                      refine ⟨1800417732340391314912321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38408911623261681384796181 1800417732340391314912321)
                      ·
                        rfl

theorem cell23_3506301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3506301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506301 prefixEnd_3506301 := by exact prefixLift 3506301
  have htrace : WordTrace (prefixWord ++ tailWord_3506301) baseStart_3506301 baseEnd_3506301 := by
    simpa [prefixWord, tailWord_3506301, baseEnd_3506301] using wordTrace_append hprefix tailTrace_3506301
  have hstable : (prefixWord ++ tailWord_3506301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506301).length < 2 ^ (prefixWord ++ tailWord_3506301).sum := by decide
  have hdescent : baseEnd_3506301 < baseStart_3506301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506308 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3506308 : Nat := 118140960795 + 3506308 * 2 ^ 59
def prefixEnd_3506308 : Nat := 4983230072969 + 3 ^ 40 * 3506308 * 2
def baseEnd_3506308 : Nat := 1800421326704972787524789

theorem tailTrace_3506308 : CollatzResearch.WordTrace tailWord_3506308 prefixEnd_3506308 1800421326704972787524789 := by
  unfold tailWord_3506308
  simp only [CollatzResearch.WordTrace]
  refine ⟨63942779490626210288119789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85257039320834947050826385 63942779490626210288119789)
  ·
    refine ⟨23978542308984828858044921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63942779490626210288119789 23978542308984828858044921)
    ·
      refine ⟨17983906731738621643533691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23978542308984828858044921 17983906731738621643533691)
      ·
        refine ⟨26975860097607932465300537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983906731738621643533691 26975860097607932465300537)
        ·
          refine ⟨20231895073205949348975403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975860097607932465300537 20231895073205949348975403)
          ·
            refine ⟨30347842609808924023463105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231895073205949348975403 30347842609808924023463105)
            ·
              refine ⟨22760881957356693017597329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30347842609808924023463105 22760881957356693017597329)
              ·
                refine ⟨17070661468017519763197997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22760881957356693017597329 17070661468017519763197997)
                ·
                  refine ⟨6401498050506569911199249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17070661468017519763197997 6401498050506569911199249)
                  ·
                    refine ⟨4801123537879927433399437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6401498050506569911199249 4801123537879927433399437)
                    ·
                      refine ⟨1800421326704972787524789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801123537879927433399437 1800421326704972787524789)
                      ·
                        rfl

theorem cell23_3506308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3506308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506308 prefixEnd_3506308 := by exact prefixLift 3506308
  have htrace : WordTrace (prefixWord ++ tailWord_3506308) baseStart_3506308 baseEnd_3506308 := by
    simpa [prefixWord, tailWord_3506308, baseEnd_3506308] using wordTrace_append hprefix tailTrace_3506308
  have hstable : (prefixWord ++ tailWord_3506308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506308).length < 2 ^ (prefixWord ++ tailWord_3506308).sum := by decide
  have hdescent : baseEnd_3506308 < baseStart_3506308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506321 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_3506321 : Nat := 118140960795 + 3506321 * 2 ^ 59
def prefixEnd_3506321 : Nat := 4983230072969 + 3 ^ 40 * 3506321 * 2
def baseEnd_3506321 : Nat := 1800428001953481236662229

theorem tailTrace_3506321 : CollatzResearch.WordTrace tailWord_3506321 prefixEnd_3506321 1800428001953481236662229 := by
  unfold tailWord_3506321
  simp only [CollatzResearch.WordTrace]
  refine ⟨127886033130205323796462817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85257355420136882530975211 127886033130205323796462817)
  ·
    refine ⟨95914524847653992847347113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127886033130205323796462817 95914524847653992847347113)
    ·
      refine ⟨71935893635740494635510335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95914524847653992847347113 71935893635740494635510335)
      ·
        refine ⟨107903840453610741953265503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71935893635740494635510335 107903840453610741953265503)
        ·
          refine ⟨161855760680416112929898255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107903840453610741953265503 161855760680416112929898255)
          ·
            refine ⟨242783641020624169394847383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161855760680416112929898255 242783641020624169394847383)
            ·
              refine ⟨364175461530936254092271075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242783641020624169394847383 364175461530936254092271075)
              ·
                refine ⟨546263192296404381138406613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364175461530936254092271075 546263192296404381138406613)
                ·
                  refine ⟨12803043569446977682931405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 546263192296404381138406613 12803043569446977682931405)
                  ·
                    refine ⟨4801141338542616631099277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12803043569446977682931405 4801141338542616631099277)
                    ·
                      refine ⟨1800428001953481236662229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801141338542616631099277 1800428001953481236662229)
                      ·
                        rfl

theorem cell23_3506321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_3506321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506321 prefixEnd_3506321 := by exact prefixLift 3506321
  have htrace : WordTrace (prefixWord ++ tailWord_3506321) baseStart_3506321 baseEnd_3506321 := by
    simpa [prefixWord, tailWord_3506321, baseEnd_3506321] using wordTrace_append hprefix tailTrace_3506321
  have hstable : (prefixWord ++ tailWord_3506321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506321).length < 2 ^ (prefixWord ++ tailWord_3506321).sum := by decide
  have hdescent : baseEnd_3506321 < baseStart_3506321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506350 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3506350 : Nat := 118140960795 + 3506350 * 2 ^ 59
def prefixEnd_3506350 : Nat := 4983230072969 + 3 ^ 40 * 3506350 * 2
def baseEnd_3506350 : Nat := 1800442892892461623199597

theorem tailTrace_3506350 : CollatzResearch.WordTrace tailWord_3506350 prefixEnd_3506350 1800442892892461623199597 := by
  unfold tailWord_3506350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985886355887532718658563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85258060564733507832845669 15985886355887532718658563)
  ·
    refine ⟨23978829533831299077987845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15985886355887532718658563 23978829533831299077987845)
    ·
      refine ⟨4496030537593368577122721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23978829533831299077987845 4496030537593368577122721)
      ·
        refine ⟨3372022903195026432842041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4496030537593368577122721 3372022903195026432842041)
        ·
          refine ⟨2529017177396269824631531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3372022903195026432842041 2529017177396269824631531)
          ·
            refine ⟨3793525766094404736947297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529017177396269824631531 3793525766094404736947297)
            ·
              refine ⟨2845144324570803552710473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3793525766094404736947297 2845144324570803552710473)
              ·
                refine ⟨2133858243428102664532855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845144324570803552710473 2133858243428102664532855)
                ·
                  refine ⟨3200787365142153996799283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133858243428102664532855 3200787365142153996799283)
                  ·
                    refine ⟨4801181047713230995198925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200787365142153996799283 4801181047713230995198925)
                    ·
                      refine ⟨1800442892892461623199597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801181047713230995198925 1800442892892461623199597)
                      ·
                        rfl

theorem cell23_3506350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3506350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506350 prefixEnd_3506350 := by exact prefixLift 3506350
  have htrace : WordTrace (prefixWord ++ tailWord_3506350) baseStart_3506350 baseEnd_3506350 := by
    simpa [prefixWord, tailWord_3506350, baseEnd_3506350] using wordTrace_append hprefix tailTrace_3506350
  have hstable : (prefixWord ++ tailWord_3506350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506350).length < 2 ^ (prefixWord ++ tailWord_3506350).sum := by decide
  have hdescent : baseEnd_3506350 < baseStart_3506350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506361 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3506361 : Nat := 118140960795 + 3506361 * 2 ^ 59
def prefixEnd_3506361 : Nat := 4983230072969 + 3 ^ 40 * 3506361 * 2
def baseEnd_3506361 : Nat := 1800448541179661080162045

theorem tailTrace_3506361 : CollatzResearch.WordTrace tailWord_3506361 prefixEnd_3506361 1800448541179661080162045 := by
  unfold tailWord_3506361
  simp only [CollatzResearch.WordTrace]
  refine ⟨127887492050060410627918937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85258328033373607085279291 127887492050060410627918937)
  ·
    refine ⟨95915619037545307970939203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127887492050060410627918937 95915619037545307970939203)
    ·
      refine ⟨143873428556317961956408805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95915619037545307970939203 143873428556317961956408805)
      ·
        refine ⟨26976267854309617866826651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143873428556317961956408805 26976267854309617866826651)
        ·
          refine ⟨40464401781464426800239977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26976267854309617866826651 40464401781464426800239977)
          ·
            refine ⟨30348301336098320100179983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40464401781464426800239977 30348301336098320100179983)
            ·
              refine ⟨45522452004147480150269975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30348301336098320100179983 45522452004147480150269975)
              ·
                refine ⟨68283678006221220225404963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45522452004147480150269975 68283678006221220225404963)
                ·
                  refine ⟨102425517009331830338107445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68283678006221220225404963 102425517009331830338107445)
                  ·
                    refine ⟨9602392219624859094197573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102425517009331830338107445 9602392219624859094197573)
                    ·
                      refine ⟨1800448541179661080162045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9602392219624859094197573 1800448541179661080162045)
                      ·
                        rfl

theorem cell23_3506361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3506361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506361 prefixEnd_3506361 := by exact prefixLift 3506361
  have htrace : WordTrace (prefixWord ++ tailWord_3506361) baseStart_3506361 baseEnd_3506361 := by
    simpa [prefixWord, tailWord_3506361, baseEnd_3506361] using wordTrace_append hprefix tailTrace_3506361
  have hstable : (prefixWord ++ tailWord_3506361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506361).length < 2 ^ (prefixWord ++ tailWord_3506361).sum := by decide
  have hdescent : baseEnd_3506361 < baseStart_3506361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506372 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3506372 : Nat := 118140960795 + 3506372 * 2 ^ 59
def prefixEnd_3506372 : Nat := 4983230072969 + 3 ^ 40 * 3506372 * 2
def baseEnd_3506372 : Nat := 1800454189466860537124495

theorem tailTrace_3506372 : CollatzResearch.WordTrace tailWord_3506372 prefixEnd_3506372 1800454189466860537124495 := by
  unfold tailWord_3506372
  simp only [CollatzResearch.WordTrace]
  refine ⟨63943946626510279753284685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85258595502013706337712913 63943946626510279753284685)
  ·
    refine ⟨23978979984941354907481757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63943946626510279753284685 23978979984941354907481757)
    ·
      refine ⟨8992117494353008090305659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23978979984941354907481757 8992117494353008090305659)
      ·
        refine ⟨13488176241529512135458489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8992117494353008090305659 13488176241529512135458489)
        ·
          refine ⟨10116132181147134101593867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13488176241529512135458489 10116132181147134101593867)
          ·
            refine ⟨15174198271720701152390801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10116132181147134101593867 15174198271720701152390801)
            ·
              refine ⟨11380648703790525864293101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15174198271720701152390801 11380648703790525864293101)
              ·
                refine ⟨4267743263921447199109913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11380648703790525864293101 4267743263921447199109913)
                ·
                  refine ⟨3200807447941085399332435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4267743263921447199109913 3200807447941085399332435)
                  ·
                    refine ⟨4801211171911628098998653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200807447941085399332435 4801211171911628098998653)
                    ·
                      refine ⟨1800454189466860537124495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801211171911628098998653 1800454189466860537124495)
                      ·
                        rfl

theorem cell23_3506372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3506372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506372 prefixEnd_3506372 := by exact prefixLift 3506372
  have htrace : WordTrace (prefixWord ++ tailWord_3506372) baseStart_3506372 baseEnd_3506372 := by
    simpa [prefixWord, tailWord_3506372, baseEnd_3506372] using wordTrace_append hprefix tailTrace_3506372
  have hstable : (prefixWord ++ tailWord_3506372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506372).length < 2 ^ (prefixWord ++ tailWord_3506372).sum := by decide
  have hdescent : baseEnd_3506372 < baseStart_3506372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506391 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3506391 : Nat := 118140960795 + 3506391 * 2 ^ 59
def prefixEnd_3506391 : Nat := 4983230072969 + 3 ^ 40 * 3506391 * 2
def baseEnd_3506391 : Nat := 1800463945599295962786907

theorem tailTrace_3506391 : CollatzResearch.WordTrace tailWord_3506391 prefixEnd_3506391 1800463945599295962786907 := by
  unfold tailWord_3506391
  simp only [CollatzResearch.WordTrace]
  refine ⟨127888586239951725751511027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85259057493301150501007351 127888586239951725751511027)
  ·
    refine ⟨191832879359927588627266541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127888586239951725751511027 191832879359927588627266541)
    ·
      refine ⟨71937329759972845735224953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191832879359927588627266541 71937329759972845735224953)
      ·
        refine ⟨53952997319979634301418715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71937329759972845735224953 53952997319979634301418715)
        ·
          refine ⟨80929495979969451452128073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53952997319979634301418715 80929495979969451452128073)
          ·
            refine ⟨60697121984977088589096055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80929495979969451452128073 60697121984977088589096055)
            ·
              refine ⟨91045682977465632883644083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60697121984977088589096055 91045682977465632883644083)
              ·
                refine ⟨136568524466198449325466125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91045682977465632883644083 136568524466198449325466125)
                ·
                  refine ⟨51213196674824418497049797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136568524466198449325466125 51213196674824418497049797)
                  ·
                    refine ⟨9602474376529578468196837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51213196674824418497049797 9602474376529578468196837)
                    ·
                      refine ⟨1800463945599295962786907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9602474376529578468196837 1800463945599295962786907)
                      ·
                        rfl

theorem cell23_3506391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3506391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506391 prefixEnd_3506391 := by exact prefixLift 3506391
  have htrace : WordTrace (prefixWord ++ tailWord_3506391) baseStart_3506391 baseEnd_3506391 := by
    simpa [prefixWord, tailWord_3506391, baseEnd_3506391] using wordTrace_append hprefix tailTrace_3506391
  have hstable : (prefixWord ++ tailWord_3506391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506391).length < 2 ^ (prefixWord ++ tailWord_3506391).sum := by decide
  have hdescent : baseEnd_3506391 < baseStart_3506391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506401 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 9]
def baseStart_3506401 : Nat := 118140960795 + 3506401 * 2 ^ 59
def prefixEnd_3506401 : Nat := 4983230072969 + 3 ^ 40 * 3506401 * 2
def baseEnd_3506401 : Nat := 200052120045093435962429

theorem tailTrace_3506401 : CollatzResearch.WordTrace tailWord_3506401 prefixEnd_3506401 200052120045093435962429 := by
  unfold tailWord_3506401
  simp only [CollatzResearch.WordTrace]
  refine ⟨127888950969915497459375057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85259300646610331639583371 127888950969915497459375057)
  ·
    refine ⟨95916713227436623094531293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127888950969915497459375057 95916713227436623094531293)
    ·
      refine ⟨35968767460288733660449235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95916713227436623094531293 35968767460288733660449235)
      ·
        refine ⟨53953151190433100490673853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35968767460288733660449235 53953151190433100490673853)
        ·
          refine ⟨20232431696412412684002695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53953151190433100490673853 20232431696412412684002695)
          ·
            refine ⟨30348647544618619026004043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20232431696412412684002695 30348647544618619026004043)
            ·
              refine ⟨45522971316927928539006065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30348647544618619026004043 45522971316927928539006065)
              ·
                refine ⟨34142228487695946404254549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45522971316927928539006065 34142228487695946404254549)
                ·
                  refine ⟨200052120045093435962429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34142228487695946404254549 200052120045093435962429)
                  ·
                    rfl

theorem cell23_3506401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_3506401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506401 prefixEnd_3506401 := by exact prefixLift 3506401
  have htrace : WordTrace (prefixWord ++ tailWord_3506401) baseStart_3506401 baseEnd_3506401 := by
    simpa [prefixWord, tailWord_3506401, baseEnd_3506401] using wordTrace_append hprefix tailTrace_3506401
  have hstable : (prefixWord ++ tailWord_3506401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506401).length < 2 ^ (prefixWord ++ tailWord_3506401).sum := by decide
  have hdescent : baseEnd_3506401 < baseStart_3506401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506408 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3506408 : Nat := 118140960795 + 3506408 * 2 ^ 59
def prefixEnd_3506408 : Nat := 4983230072969 + 3 ^ 40 * 3506408 * 2
def baseEnd_3506408 : Nat := 1800472674770422396274329

theorem tailTrace_3506408 : CollatzResearch.WordTrace tailWord_3506408 prefixEnd_3506408 1800472674770422396274329 := by
  unfold tailWord_3506408
  simp only [CollatzResearch.WordTrace]
  refine ⟨63944603140445068827439939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85259470853926758436586585 63944603140445068827439939)
  ·
    refine ⟨95916904710667603241159909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63944603140445068827439939 95916904710667603241159909)
    ·
      refine ⟨17984419633250175607717483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95916904710667603241159909 17984419633250175607717483)
      ·
        refine ⟨26976629449875263411576225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17984419633250175607717483 26976629449875263411576225)
        ·
          refine ⟨20232472087406447558682169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26976629449875263411576225 20232472087406447558682169)
          ·
            refine ⟨15174354065554835669011627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20232472087406447558682169 15174354065554835669011627)
            ·
              refine ⟨22761531098332253503517441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15174354065554835669011627 22761531098332253503517441)
              ·
                refine ⟨17071148323749190127638081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22761531098332253503517441 17071148323749190127638081)
                ·
                  refine ⟨12803361242811892595728561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17071148323749190127638081 12803361242811892595728561)
                  ·
                    refine ⟨9602520932108919446796421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12803361242811892595728561 9602520932108919446796421)
                    ·
                      refine ⟨1800472674770422396274329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9602520932108919446796421 1800472674770422396274329)
                      ·
                        rfl

theorem cell23_3506408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3506408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506408 prefixEnd_3506408 := by exact prefixLift 3506408
  have htrace : WordTrace (prefixWord ++ tailWord_3506408) baseStart_3506408 baseEnd_3506408 := by
    simpa [prefixWord, tailWord_3506408, baseEnd_3506408] using wordTrace_append hprefix tailTrace_3506408
  have hstable : (prefixWord ++ tailWord_3506408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506408).length < 2 ^ (prefixWord ++ tailWord_3506408).sum := by decide
  have hdescent : baseEnd_3506408 < baseStart_3506408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506418 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 7]
def baseStart_3506418 : Nat := 118140960795 + 3506418 * 2 ^ 59
def prefixEnd_3506418 : Nat := 4983230072969 + 3 ^ 40 * 3506418 * 2
def baseEnd_3506418 : Nat := 200053089952996373016587

theorem tailTrace_3506418 : CollatzResearch.WordTrace tailWord_3506418 prefixEnd_3506418 200053089952996373016587 := by
  unfold tailWord_3506418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31972392752713477340685977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85259714007235939575162605 31972392752713477340685977)
  ·
    refine ⟨23979294564535108005514483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31972392752713477340685977 23979294564535108005514483)
    ·
      refine ⟨35968941846802662008271725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23979294564535108005514483 35968941846802662008271725)
      ·
        refine ⟨13488353192550998253101897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35968941846802662008271725 13488353192550998253101897)
        ·
          refine ⟨10116264894413248689826423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13488353192550998253101897 10116264894413248689826423)
          ·
            refine ⟨15174397341619873034739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10116264894413248689826423 15174397341619873034739635)
            ·
              refine ⟨22761596012429809552109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15174397341619873034739635 22761596012429809552109453)
              ·
                refine ⟨8535598504661178582041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22761596012429809552109453 8535598504661178582041045)
                ·
                  refine ⟨200053089952996373016587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8535598504661178582041045 200053089952996373016587)
                  ·
                    rfl

theorem cell23_3506418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_3506418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506418 prefixEnd_3506418 := by exact prefixLift 3506418
  have htrace : WordTrace (prefixWord ++ tailWord_3506418) baseStart_3506418 baseEnd_3506418 := by
    simpa [prefixWord, tailWord_3506418, baseEnd_3506418] using wordTrace_append hprefix tailTrace_3506418
  have hstable : (prefixWord ++ tailWord_3506418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506418).length < 2 ^ (prefixWord ++ tailWord_3506418).sum := by decide
  have hdescent : baseEnd_3506418 < baseStart_3506418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506431 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 7]
def baseStart_3506431 : Nat := 118140960795 + 3506431 * 2 ^ 59
def prefixEnd_3506431 : Nat := 4983230072969 + 3 ^ 40 * 3506431 * 2
def baseEnd_3506431 : Nat := 600161494941825268762241

theorem tailTrace_3506431 : CollatzResearch.WordTrace tailWord_3506431 prefixEnd_3506431 600161494941825268762241 := by
  unfold tailWord_3506431
  simp only [CollatzResearch.WordTrace]
  refine ⟨127890045159806812582967147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85260030106537875055311431 127890045159806812582967147)
  ·
    refine ⟨191835067739710218874450721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127890045159806812582967147 191835067739710218874450721)
    ·
      refine ⟨143876300804782664155838041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191835067739710218874450721 143876300804782664155838041)
      ·
        refine ⟨107907225603586998116878531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143876300804782664155838041 107907225603586998116878531)
        ·
          refine ⟨161860838405380497175317797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107907225603586998116878531 161860838405380497175317797)
          ·
            refine ⟨30348907201008843220372087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161860838405380497175317797 30348907201008843220372087)
            ·
              refine ⟨45523360801513264830558131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30348907201008843220372087 45523360801513264830558131)
              ·
                refine ⟨68285041202269897245837197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45523360801513264830558131 68285041202269897245837197)
                ·
                  refine ⟨25606890450851211467188949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68285041202269897245837197 25606890450851211467188949)
                  ·
                    refine ⟨600161494941825268762241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25606890450851211467188949 600161494941825268762241)
                    ·
                      rfl

theorem cell23_3506431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_3506431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506431 prefixEnd_3506431 := by exact prefixLift 3506431
  have htrace : WordTrace (prefixWord ++ tailWord_3506431) baseStart_3506431 baseEnd_3506431 := by
    simpa [prefixWord, tailWord_3506431, baseEnd_3506431] using wordTrace_append hprefix tailTrace_3506431
  have hstable : (prefixWord ++ tailWord_3506431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506431).length < 2 ^ (prefixWord ++ tailWord_3506431).sum := by decide
  have hdescent : baseEnd_3506431 < baseStart_3506431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506485 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_3506485 : Nat := 118140960795 + 3506485 * 2 ^ 59
def prefixEnd_3506485 : Nat := 4983230072969 + 3 ^ 40 * 3506485 * 2
def baseEnd_3506485 : Nat := 1800512212780818595011475

theorem tailTrace_3506485 : CollatzResearch.WordTrace tailWord_3506485 prefixEnd_3506485 1800512212780818595011475 := by
  unfold tailWord_3506485
  simp only [CollatzResearch.WordTrace]
  refine ⟨127892014701611179805432909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85261343134407453203621939 127892014701611179805432909)
  ·
    refine ⟨47959505513104192427037341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127892014701611179805432909 47959505513104192427037341)
    ·
      refine ⟨17984814567414072160139003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47959505513104192427037341 17984814567414072160139003)
      ·
        refine ⟨26977221851121108240208505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17984814567414072160139003 26977221851121108240208505)
        ·
          refine ⟨20232916388340831180156379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26977221851121108240208505 20232916388340831180156379)
          ·
            refine ⟨30349374582511246770234569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20232916388340831180156379 30349374582511246770234569)
            ·
              refine ⟨22762030936883435077675927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30349374582511246770234569 22762030936883435077675927)
              ·
                refine ⟨34143046405325152616513891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22762030936883435077675927 34143046405325152616513891)
                ·
                  refine ⟨51214569607987728924770837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34143046405325152616513891 51214569607987728924770837)
                  ·
                    refine ⟨2400682950374424793348633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51214569607987728924770837 2400682950374424793348633)
                    ·
                      refine ⟨1800512212780818595011475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400682950374424793348633 1800512212780818595011475)
                      ·
                        rfl

theorem cell23_3506485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_3506485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506485 prefixEnd_3506485 := by exact prefixLift 3506485
  have htrace : WordTrace (prefixWord ++ tailWord_3506485) baseStart_3506485 baseEnd_3506485 := by
    simpa [prefixWord, tailWord_3506485, baseEnd_3506485] using wordTrace_append hprefix tailTrace_3506485
  have hstable : (prefixWord ++ tailWord_3506485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506485).length < 2 ^ (prefixWord ++ tailWord_3506485).sum := by decide
  have hdescent : baseEnd_3506485 < baseStart_3506485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506488 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_3506488 : Nat := 118140960795 + 3506488 * 2 ^ 59
def prefixEnd_3506488 : Nat := 4983230072969 + 3 ^ 40 * 3506488 * 2
def baseEnd_3506488 : Nat := 1800513753222782083273961

theorem tailTrace_3506488 : CollatzResearch.WordTrace tailWord_3506488 prefixEnd_3506488 1800513753222782083273961 := by
  unfold tailWord_3506488
  simp only [CollatzResearch.WordTrace]
  refine ⟨63946062060300155658896059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85261416080400207545194745 63946062060300155658896059)
  ·
    refine ⟨95919093090450233488344089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63946062060300155658896059 95919093090450233488344089)
    ·
      refine ⟨71939319817837675116258067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95919093090450233488344089 71939319817837675116258067)
      ·
        refine ⟨107908979726756512674387101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71939319817837675116258067 107908979726756512674387101)
        ·
          refine ⟨40465867397533692252895163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107908979726756512674387101 40465867397533692252895163)
          ·
            refine ⟨60698801096300538379342745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40465867397533692252895163 60698801096300538379342745)
            ·
              refine ⟨45524100822225403784507059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60698801096300538379342745 45524100822225403784507059)
              ·
                refine ⟨68286151233338105676760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45524100822225403784507059 68286151233338105676760589)
                ·
                  refine ⟨25607306712501789628785221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68286151233338105676760589 25607306712501789628785221)
                  ·
                    refine ⟨4801370008594085555397229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25607306712501789628785221 4801370008594085555397229)
                    ·
                      refine ⟨1800513753222782083273961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801370008594085555397229 1800513753222782083273961)
                      ·
                        rfl

theorem cell23_3506488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_3506488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506488 prefixEnd_3506488 := by exact prefixLift 3506488
  have htrace : WordTrace (prefixWord ++ tailWord_3506488) baseStart_3506488 baseEnd_3506488 := by
    simpa [prefixWord, tailWord_3506488, baseEnd_3506488] using wordTrace_append hprefix tailTrace_3506488
  have hstable : (prefixWord ++ tailWord_3506488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506488).length < 2 ^ (prefixWord ++ tailWord_3506488).sum := by decide
  have hdescent : baseEnd_3506488 < baseStart_3506488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506545 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_3506545 : Nat := 118140960795 + 3506545 * 2 ^ 59
def prefixEnd_3506545 : Nat := 4983230072969 + 3 ^ 40 * 3506545 * 2
def baseEnd_3506545 : Nat := 1800543021620088360261199

theorem tailTrace_3506545 : CollatzResearch.WordTrace tailWord_3506545 prefixEnd_3506545 1800543021620088360261199 := by
  unfold tailWord_3506545
  simp only [CollatzResearch.WordTrace]
  refine ⟨127894203081393810052617089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85262802054262540035078059 127894203081393810052617089)
  ·
    refine ⟨95920652311045357539462817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127894203081393810052617089 95920652311045357539462817)
    ·
      refine ⟨71940489233284018154597113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95920652311045357539462817 71940489233284018154597113)
      ·
        refine ⟨53955366924963013615947835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71940489233284018154597113 53955366924963013615947835)
        ·
          refine ⟨80933050387444520423921753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53955366924963013615947835 80933050387444520423921753)
          ·
            refine ⟨60699787790583390317941315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80933050387444520423921753 60699787790583390317941315)
            ·
              refine ⟨91049681685875085476911973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60699787790583390317941315 91049681685875085476911973)
              ·
                refine ⟨17071815316101578526920995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91049681685875085476911973 17071815316101578526920995)
                ·
                  refine ⟨25607722974152367790381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17071815316101578526920995 25607722974152367790381493)
                  ·
                    refine ⟨2400724028826784480348265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25607722974152367790381493 2400724028826784480348265)
                    ·
                      refine ⟨1800543021620088360261199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400724028826784480348265 1800543021620088360261199)
                      ·
                        rfl

theorem cell23_3506545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_3506545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506545 prefixEnd_3506545 := by exact prefixLift 3506545
  have htrace : WordTrace (prefixWord ++ tailWord_3506545) baseStart_3506545 baseEnd_3506545 := by
    simpa [prefixWord, tailWord_3506545, baseEnd_3506545] using wordTrace_append hprefix tailTrace_3506545
  have hstable : (prefixWord ++ tailWord_3506545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506545).length < 2 ^ (prefixWord ++ tailWord_3506545).sum := by decide
  have hdescent : baseEnd_3506545 < baseStart_3506545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506569 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 1, 1, 3]
def baseStart_3506569 : Nat := 118140960795 + 3506569 * 2 ^ 59
def prefixEnd_3506569 : Nat := 4983230072969 + 3 ^ 40 * 3506569 * 2
def baseEnd_3506569 : Nat := 1800555345155796266361089

theorem tailTrace_3506569 : CollatzResearch.WordTrace tailWord_3506569 prefixEnd_3506569 1800555345155796266361089 := by
  unfold tailWord_3506569
  simp only [CollatzResearch.WordTrace]
  refine ⟨127895078433306862151490761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85263385622204574767660507 127895078433306862151490761)
  ·
    refine ⟨95921308824980146613618071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127895078433306862151490761 95921308824980146613618071)
    ·
      refine ⟨143881963237470219920427107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95921308824980146613618071 143881963237470219920427107)
      ·
        refine ⟨215822944856205329880640661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143881963237470219920427107 215822944856205329880640661)
        ·
          refine ⟨10116700540134624838155031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215822944856205329880640661 10116700540134624838155031)
          ·
            refine ⟨15175050810201937257232547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10116700540134624838155031 15175050810201937257232547)
            ·
              refine ⟨22762576215302905885848821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15175050810201937257232547 22762576215302905885848821)
              ·
                refine ⟨2133991520184647426798327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22762576215302905885848821 2133991520184647426798327)
                ·
                  refine ⟨3200987280276971140197491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133991520184647426798327 3200987280276971140197491)
                  ·
                    refine ⟨4801480920415456710296237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200987280276971140197491 4801480920415456710296237)
                    ·
                      refine ⟨1800555345155796266361089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801480920415456710296237 1800555345155796266361089)
                      ·
                        rfl

theorem cell23_3506569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 1, 3].length) (baseStart_3506569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506569 prefixEnd_3506569 := by exact prefixLift 3506569
  have htrace : WordTrace (prefixWord ++ tailWord_3506569) baseStart_3506569 baseEnd_3506569 := by
    simpa [prefixWord, tailWord_3506569, baseEnd_3506569] using wordTrace_append hprefix tailTrace_3506569
  have hstable : (prefixWord ++ tailWord_3506569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506569).length < 2 ^ (prefixWord ++ tailWord_3506569).sum := by decide
  have hdescent : baseEnd_3506569 < baseStart_3506569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506572 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_3506572 : Nat := 118140960795 + 3506572 * 2 ^ 59
def prefixEnd_3506572 : Nat := 4983230072969 + 3 ^ 40 * 3506572 * 2
def baseEnd_3506572 : Nat := 600185628532586584874525

theorem tailTrace_3506572 : CollatzResearch.WordTrace tailWord_3506572 prefixEnd_3506572 600185628532586584874525 := by
  unfold tailWord_3506572
  simp only [CollatzResearch.WordTrace]
  refine ⟨63947593926147996831924985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85263458568197329109233313 63947593926147996831924985)
  ·
    refine ⟨47960695444610997623943739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63947593926147996831924985 47960695444610997623943739)
    ·
      refine ⟨71941043166916496435915609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47960695444610997623943739 71941043166916496435915609)
      ·
        refine ⟨53955782375187372326936707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71941043166916496435915609 53955782375187372326936707)
        ·
          refine ⟨80933673562781058490405061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53955782375187372326936707 80933673562781058490405061)
          ·
            refine ⟨15175063793021448466950949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80933673562781058490405061 15175063793021448466950949)
            ·
              refine ⟨2845324461191521587553303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15175063793021448466950949 2845324461191521587553303)
              ·
                refine ⟨4267986691787282381329955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845324461191521587553303 4267986691787282381329955)
                ·
                  refine ⟨6401980037680923571994933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267986691787282381329955 6401980037680923571994933)
                  ·
                    refine ⟨600185628532586584874525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6401980037680923571994933 600185628532586584874525)
                    ·
                      rfl

theorem cell23_3506572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_3506572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506572 prefixEnd_3506572 := by exact prefixLift 3506572
  have htrace : WordTrace (prefixWord ++ tailWord_3506572) baseStart_3506572 baseEnd_3506572 := by
    simpa [prefixWord, tailWord_3506572, baseEnd_3506572] using wordTrace_append hprefix tailTrace_3506572
  have hstable : (prefixWord ++ tailWord_3506572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506572).length < 2 ^ (prefixWord ++ tailWord_3506572).sum := by decide
  have hdescent : baseEnd_3506572 < baseStart_3506572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506585 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_3506585 : Nat := 118140960795 + 3506585 * 2 ^ 59
def prefixEnd_3506585 : Nat := 4983230072969 + 3 ^ 40 * 3506585 * 2
def baseEnd_3506585 : Nat := 600187853615422734587005

theorem tailTrace_3506585 : CollatzResearch.WordTrace tailWord_3506585 prefixEnd_3506585 600187853615422734587005 := by
  unfold tailWord_3506585
  simp only [CollatzResearch.WordTrace]
  refine ⟨127895662001248896884073209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85263774667499264589382139 127895662001248896884073209)
  ·
    refine ⟨95921746500936672663054907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127895662001248896884073209 95921746500936672663054907)
    ·
      refine ⟨143882619751405008994582361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95921746500936672663054907 143882619751405008994582361)
      ·
        refine ⟨107911964813553756745936771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143882619751405008994582361 107911964813553756745936771)
        ·
          refine ⟨161867947220330635118905157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107911964813553756745936771 161867947220330635118905157)
          ·
            refine ⟨30350240103811994084794717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161867947220330635118905157 30350240103811994084794717)
            ·
              refine ⟨11381340038929497781798019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30350240103811994084794717 11381340038929497781798019)
              ·
                refine ⟨17072010058394246672697029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381340038929497781798019 17072010058394246672697029)
                ·
                  refine ⟨3201001885948921251130693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17072010058394246672697029 3201001885948921251130693)
                  ·
                    refine ⟨600187853615422734587005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3201001885948921251130693 600187853615422734587005)
                    ·
                      rfl

theorem cell23_3506585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_3506585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506585 prefixEnd_3506585 := by exact prefixLift 3506585
  have htrace : WordTrace (prefixWord ++ tailWord_3506585) baseStart_3506585 baseEnd_3506585 := by
    simpa [prefixWord, tailWord_3506585, baseEnd_3506585] using wordTrace_append hprefix tailTrace_3506585
  have hstable : (prefixWord ++ tailWord_3506585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506585).length < 2 ^ (prefixWord ++ tailWord_3506585).sum := by decide
  have hdescent : baseEnd_3506585 < baseStart_3506585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506595 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5]
def baseStart_3506595 : Nat := 118140960795 + 3506595 * 2 ^ 59
def prefixEnd_3506595 : Nat := 4983230072969 + 3 ^ 40 * 3506595 * 2
def baseEnd_3506595 : Nat := 1800568695652813164635969

theorem tailTrace_3506595 : CollatzResearch.WordTrace tailWord_3506595 prefixEnd_3506595 1800568695652813164635969 := by
  unfold tailWord_3506595
  simp only [CollatzResearch.WordTrace]
  refine ⟨127896026731212668591937239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85264017820808445727958159 127896026731212668591937239)
  ·
    refine ⟨191844040096819002887905859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127896026731212668591937239 191844040096819002887905859)
    ·
      refine ⟨287766060145228504331858789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191844040096819002887905859 287766060145228504331858789)
      ·
        refine ⟨53956136277230344562223523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287766060145228504331858789 53956136277230344562223523)
        ·
          refine ⟨80934204415845516843335285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53956136277230344562223523 80934204415845516843335285)
          ·
            refine ⟨7587581663985517204062683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80934204415845516843335285 7587581663985517204062683)
            ·
              refine ⟨11381372495978275806094025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587581663985517204062683 11381372495978275806094025)
              ·
                refine ⟨8536029371983706854570519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11381372495978275806094025 8536029371983706854570519)
                ·
                  refine ⟨12804044057975560281855779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8536029371983706854570519 12804044057975560281855779)
                  ·
                    refine ⟨19206066086963340422783669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12804044057975560281855779 19206066086963340422783669)
                    ·
                      refine ⟨1800568695652813164635969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19206066086963340422783669 1800568695652813164635969)
                      ·
                        rfl

theorem cell23_3506595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_3506595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506595 prefixEnd_3506595 := by exact prefixLift 3506595
  have htrace : WordTrace (prefixWord ++ tailWord_3506595) baseStart_3506595 baseEnd_3506595 := by
    simpa [prefixWord, tailWord_3506595, baseEnd_3506595] using wordTrace_append hprefix tailTrace_3506595
  have hstable : (prefixWord ++ tailWord_3506595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506595).length < 2 ^ (prefixWord ++ tailWord_3506595).sum := by decide
  have hdescent : baseEnd_3506595 < baseStart_3506595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506609 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_3506609 : Nat := 118140960795 + 3506609 * 2 ^ 59
def prefixEnd_3506609 : Nat := 4983230072969 + 3 ^ 40 * 3506609 * 2
def baseEnd_3506609 : Nat := 1800575884381976109860905

theorem tailTrace_3506609 : CollatzResearch.WordTrace tailWord_3506609 prefixEnd_3506609 1800575884381976109860905 := by
  unfold tailWord_3506609
  simp only [CollatzResearch.WordTrace]
  refine ⟨127896537353161948982946881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85264358235441299321964587 127896537353161948982946881)
  ·
    refine ⟨95922403014871461737210161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127896537353161948982946881 95922403014871461737210161)
    ·
      refine ⟨71941802261153596302907621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95922403014871461737210161 71941802261153596302907621)
      ·
        refine ⟨13489087923966299306795179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71941802261153596302907621 13489087923966299306795179)
        ·
          refine ⟨20233631885949448960192769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13489087923966299306795179 20233631885949448960192769)
          ·
            refine ⟨15175223914462086720144577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20233631885949448960192769 15175223914462086720144577)
            ·
              refine ⟨11381417935846565040108433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15175223914462086720144577 11381417935846565040108433)
              ·
                refine ⟨8536063451884923780081325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11381417935846565040108433 8536063451884923780081325)
                ·
                  refine ⟨3201023794456846417530497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8536063451884923780081325 3201023794456846417530497)
                  ·
                    refine ⟨2400767845842634813147873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3201023794456846417530497 2400767845842634813147873)
                    ·
                      refine ⟨1800575884381976109860905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400767845842634813147873 1800575884381976109860905)
                      ·
                        rfl

theorem cell23_3506609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_3506609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506609 prefixEnd_3506609 := by exact prefixLift 3506609
  have htrace : WordTrace (prefixWord ++ tailWord_3506609) baseStart_3506609 baseEnd_3506609 := by
    simpa [prefixWord, tailWord_3506609, baseEnd_3506609] using wordTrace_append hprefix tailTrace_3506609
  have hstable : (prefixWord ++ tailWord_3506609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506609).length < 2 ^ (prefixWord ++ tailWord_3506609).sum := by decide
  have hdescent : baseEnd_3506609 < baseStart_3506609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506615 : List Nat := [1, 1, 3, 1, 3, 3, 4, 7]
def baseStart_3506615 : Nat := 118140960795 + 3506615 * 2 ^ 59
def prefixEnd_3506615 : Nat := 4983230072969 + 3 ^ 40 * 3506615 * 2
def baseEnd_3506615 : Nat := 66688109824663077273551

theorem tailTrace_3506615 : CollatzResearch.WordTrace tailWord_3506615 prefixEnd_3506615 66688109824663077273551 := by
  unfold tailWord_3506615
  simp only [CollatzResearch.WordTrace]
  refine ⟨127896756191140212007665299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85264504127426808005110199 127896756191140212007665299)
  ·
    refine ⟨191845134286710318011497949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127896756191140212007665299 191845134286710318011497949)
    ·
      refine ⟨71941925357516369254311731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191845134286710318011497949 71941925357516369254311731)
      ·
        refine ⟨107912888036274553881467597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71941925357516369254311731 107912888036274553881467597)
        ·
          refine ⟨40467333013602957705550349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107912888036274553881467597 40467333013602957705550349)
          ·
            refine ⟨15175249880101109139581381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40467333013602957705550349 15175249880101109139581381)
            ·
              refine ⟨2845359352518957963671509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15175249880101109139581381 2845359352518957963671509)
              ·
                refine ⟨66688109824663077273551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2845359352518957963671509 66688109824663077273551)
                ·
                  rfl

theorem cell23_3506615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 7].length) (baseStart_3506615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506615 prefixEnd_3506615 := by exact prefixLift 3506615
  have htrace : WordTrace (prefixWord ++ tailWord_3506615) baseStart_3506615 baseEnd_3506615 := by
    simpa [prefixWord, tailWord_3506615, baseEnd_3506615] using wordTrace_append hprefix tailTrace_3506615
  have hstable : (prefixWord ++ tailWord_3506615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506615).length < 2 ^ (prefixWord ++ tailWord_3506615).sum := by decide
  have hdescent : baseEnd_3506615 < baseStart_3506615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3506618 : Nat := 118140960795 + 3506618 * 2 ^ 59
def prefixEnd_3506618 : Nat := 4983230072969 + 3 ^ 40 * 3506618 * 2
def baseEnd_3506618 : Nat := 1800580505707866574648363

theorem tailTrace_3506618 : CollatzResearch.WordTrace tailWord_3506618 prefixEnd_3506618 1800580505707866574648363 := by
  unfold tailWord_3506618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31974216402532335880006127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85264577073419562346683005 31974216402532335880006127)
  ·
    refine ⟨47961324603798503820009191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31974216402532335880006127 47961324603798503820009191)
    ·
      refine ⟨71941986905697755730013787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47961324603798503820009191 71941986905697755730013787)
      ·
        refine ⟨107912980358546633595020681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71941986905697755730013787 107912980358546633595020681)
        ·
          refine ⟨80934735268909975196265511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107912980358546633595020681 80934735268909975196265511)
          ·
            refine ⟨121402102903364962794398267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80934735268909975196265511 121402102903364962794398267)
            ·
              refine ⟨182103154355047444191597401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121402102903364962794398267 182103154355047444191597401)
              ·
                refine ⟨136577365766285583143698051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182103154355047444191597401 136577365766285583143698051)
                ·
                  refine ⟨204866048649428374715547077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136577365766285583143698051 204866048649428374715547077)
                  ·
                    refine ⟨38412384121767820259165077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204866048649428374715547077 38412384121767820259165077)
                    ·
                      refine ⟨1800580505707866574648363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38412384121767820259165077 1800580505707866574648363)
                      ·
                        rfl

theorem cell23_3506618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3506618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506618 prefixEnd_3506618 := by exact prefixLift 3506618
  have htrace : WordTrace (prefixWord ++ tailWord_3506618) baseStart_3506618 baseEnd_3506618 := by
    simpa [prefixWord, tailWord_3506618, baseEnd_3506618] using wordTrace_append hprefix tailTrace_3506618
  have hstable : (prefixWord ++ tailWord_3506618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506618).length < 2 ^ (prefixWord ++ tailWord_3506618).sum := by decide
  have hdescent : baseEnd_3506618 < baseStart_3506618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506685 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3506685 : Nat := 118140960795 + 3506685 * 2 ^ 59
def prefixEnd_3506685 : Nat := 4983230072969 + 3 ^ 40 * 3506685 * 2
def baseEnd_3506685 : Nat := 1800614908911717812510555

theorem tailTrace_3506685 : CollatzResearch.WordTrace tailWord_3506685 prefixEnd_3506685 1800614908911717812510555 := by
  unfold tailWord_3506685
  simp only [CollatzResearch.WordTrace]
  refine ⟨127899309300886613962713509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85266206200591075975142339 127899309300886613962713509)
  ·
    refine ⟨23981120493916240118008783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127899309300886613962713509 23981120493916240118008783)
    ·
      refine ⟨35971680740874360177013175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23981120493916240118008783 35971680740874360177013175)
      ·
        refine ⟨53957521111311540265519763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35971680740874360177013175 53957521111311540265519763)
        ·
          refine ⟨80936281666967310398279645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53957521111311540265519763 80936281666967310398279645)
          ·
            refine ⟨30351105625112741399354867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80936281666967310398279645 30351105625112741399354867)
            ·
              refine ⟨45526658437669112099032301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30351105625112741399354867 45526658437669112099032301)
              ·
                refine ⟨17072496914125917037137113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45526658437669112099032301 17072496914125917037137113)
                ·
                  refine ⟨12804372685594437777852835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17072496914125917037137113 12804372685594437777852835)
                  ·
                    refine ⟨19206559028391656666779253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12804372685594437777852835 19206559028391656666779253)
                    ·
                      refine ⟨1800614908911717812510555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19206559028391656666779253 1800614908911717812510555)
                      ·
                        rfl

theorem cell23_3506685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3506685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506685 prefixEnd_3506685 := by exact prefixLift 3506685
  have htrace : WordTrace (prefixWord ++ tailWord_3506685) baseStart_3506685 baseEnd_3506685 := by
    simpa [prefixWord, tailWord_3506685, baseEnd_3506685] using wordTrace_append hprefix tailTrace_3506685
  have hstable : (prefixWord ++ tailWord_3506685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506685).length < 2 ^ (prefixWord ++ tailWord_3506685).sum := by decide
  have hdescent : baseEnd_3506685 < baseStart_3506685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506694 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3506694 : Nat := 118140960795 + 3506694 * 2 ^ 59
def prefixEnd_3506694 : Nat := 4983230072969 + 3 ^ 40 * 3506694 * 2
def baseEnd_3506694 : Nat := 1800619530237608277298015

theorem tailTrace_3506694 : CollatzResearch.WordTrace tailWord_3506694 prefixEnd_3506694 1800619530237608277298015 := by
  unfold tailWord_3506694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996863673682937765618473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85266425038569338999860757 3996863673682937765618473)
  ·
    refine ⟨2997647755262203324213855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3996863673682937765618473 2997647755262203324213855)
    ·
      refine ⟨4496471632893304986320783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997647755262203324213855 4496471632893304986320783)
      ·
        refine ⟨6744707449339957479481175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4496471632893304986320783 6744707449339957479481175)
        ·
          refine ⟨10117061174009936219221763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744707449339957479481175 10117061174009936219221763)
          ·
            refine ⟨15175591761014904328832645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10117061174009936219221763 15175591761014904328832645)
            ·
              refine ⟨2845423455190294561656121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15175591761014904328832645 2845423455190294561656121)
              ·
                refine ⟨2134067591392720921242091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845423455190294561656121 2134067591392720921242091)
                ·
                  refine ⟨3201101387089081381863137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134067591392720921242091 3201101387089081381863137)
                  ·
                    refine ⟨2400826040316811036397353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3201101387089081381863137 2400826040316811036397353)
                    ·
                      refine ⟨1800619530237608277298015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400826040316811036397353 1800619530237608277298015)
                      ·
                        rfl

theorem cell23_3506694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3506694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506694 prefixEnd_3506694 := by exact prefixLift 3506694
  have htrace : WordTrace (prefixWord ++ tailWord_3506694) baseStart_3506694 baseEnd_3506694 := by
    simpa [prefixWord, tailWord_3506694, baseEnd_3506694] using wordTrace_append hprefix tailTrace_3506694
  have hstable : (prefixWord ++ tailWord_3506694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506694).length < 2 ^ (prefixWord ++ tailWord_3506694).sum := by decide
  have hdescent : baseEnd_3506694 < baseStart_3506694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506702 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3506702 : Nat := 118140960795 + 3506702 * 2 ^ 59
def prefixEnd_3506702 : Nat := 4983230072969 + 3 ^ 40 * 3506702 * 2
def baseEnd_3506702 : Nat := 1800623638082844245997977

theorem tailTrace_3506702 : CollatzResearch.WordTrace tailWord_3506702 prefixEnd_3506702 1800623638082844245997977 := by
  unfold tailWord_3506702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15987491167728128233260295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85266619561216683910721573 15987491167728128233260295)
  ·
    refine ⟨23981236751592192349890443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15987491167728128233260295 23981236751592192349890443)
    ·
      refine ⟨35971855127388288524835665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23981236751592192349890443 35971855127388288524835665)
      ·
        refine ⟨26978891345541216393626749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35971855127388288524835665 26978891345541216393626749)
        ·
          refine ⟨10117084254577956147610031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26978891345541216393626749 10117084254577956147610031)
          ·
            refine ⟨15175626381866934221415047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10117084254577956147610031 15175626381866934221415047)
            ·
              refine ⟨22763439572800401332122571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15175626381866934221415047 22763439572800401332122571)
              ·
                refine ⟨34145159359200601998183857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22763439572800401332122571 34145159359200601998183857)
                ·
                  refine ⟨25608869519400451498637893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34145159359200601998183857 25608869519400451498637893)
                  ·
                    refine ⟨4801663034887584655994605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25608869519400451498637893 4801663034887584655994605)
                    ·
                      refine ⟨1800623638082844245997977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801663034887584655994605 1800623638082844245997977)
                      ·
                        rfl

theorem cell23_3506702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3506702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506702 prefixEnd_3506702 := by exact prefixLift 3506702
  have htrace : WordTrace (prefixWord ++ tailWord_3506702) baseStart_3506702 baseEnd_3506702 := by
    simpa [prefixWord, tailWord_3506702, baseEnd_3506702] using wordTrace_append hprefix tailTrace_3506702
  have hstable : (prefixWord ++ tailWord_3506702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506702).length < 2 ^ (prefixWord ++ tailWord_3506702).sum := by decide
  have hdescent : baseEnd_3506702 < baseStart_3506702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506712 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3506712 : Nat := 118140960795 + 3506712 * 2 ^ 59
def prefixEnd_3506712 : Nat := 4983230072969 + 3 ^ 40 * 3506712 * 2
def baseEnd_3506712 : Nat := 1800628772889389206872931

theorem tailTrace_3506712 : CollatzResearch.WordTrace tailWord_3506712 prefixEnd_3506712 1800628772889389206872931 := by
  unfold tailWord_3506712
  simp only [CollatzResearch.WordTrace]
  refine ⟨63950147035894398786973195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85266862714525865049297593 63950147035894398786973195)
  ·
    refine ⟨95925220553841598180459793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63950147035894398786973195 95925220553841598180459793)
    ·
      refine ⟨71943915415381198635344845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95925220553841598180459793 71943915415381198635344845)
      ·
        refine ⟨26978968280767949488254317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71943915415381198635344845 26978968280767949488254317)
        ·
          refine ⟨10117113105287981058095369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26978968280767949488254317 10117113105287981058095369)
          ·
            refine ⟨7587834828965985793571527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10117113105287981058095369 7587834828965985793571527)
            ·
              refine ⟨11381752243448978690357291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587834828965985793571527 11381752243448978690357291)
              ·
                refine ⟨17072628365173468035535937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381752243448978690357291 17072628365173468035535937)
                ·
                  refine ⟨12804471273880101026651953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17072628365173468035535937 12804471273880101026651953)
                  ·
                    refine ⟨9603353455410075769988965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12804471273880101026651953 9603353455410075769988965)
                    ·
                      refine ⟨1800628772889389206872931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9603353455410075769988965 1800628772889389206872931)
                      ·
                        rfl

theorem cell23_3506712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3506712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506712 prefixEnd_3506712 := by exact prefixLift 3506712
  have htrace : WordTrace (prefixWord ++ tailWord_3506712) baseStart_3506712 baseEnd_3506712 := by
    simpa [prefixWord, tailWord_3506712, baseEnd_3506712] using wordTrace_append hprefix tailTrace_3506712
  have hstable : (prefixWord ++ tailWord_3506712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506712).length < 2 ^ (prefixWord ++ tailWord_3506712).sum := by decide
  have hdescent : baseEnd_3506712 < baseStart_3506712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506716 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_3506716 : Nat := 118140960795 + 3506716 * 2 ^ 59
def prefixEnd_3506716 : Nat := 4983230072969 + 3 ^ 40 * 3506716 * 2
def baseEnd_3506716 : Nat := 1800630826812007191222913

theorem tailTrace_3506716 : CollatzResearch.WordTrace tailWord_3506716 prefixEnd_3506716 1800630826812007191222913 := by
  unfold tailWord_3506716
  simp only [CollatzResearch.WordTrace]
  refine ⟨63950219981887153128546001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85266959975849537504728001 63950219981887153128546001)
  ·
    refine ⟨47962664986415364846409501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63950219981887153128546001 47962664986415364846409501)
    ·
      refine ⟨17985999369905761817403563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47962664986415364846409501 17985999369905761817403563)
      ·
        refine ⟨26978999054858642726105345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17985999369905761817403563 26978999054858642726105345)
        ·
          refine ⟨20234249291143982044579009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26978999054858642726105345 20234249291143982044579009)
          ·
            refine ⟨15175686968357986533434257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20234249291143982044579009 15175686968357986533434257)
            ·
              refine ⟨11381765226268489900075693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15175686968357986533434257 11381765226268489900075693)
              ·
                refine ⟨4268161959850683712528385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11381765226268489900075693 4268161959850683712528385)
                ·
                  refine ⟨3201121469888012784396289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4268161959850683712528385 3201121469888012784396289)
                  ·
                    refine ⟨2400841102416009588297217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3201121469888012784396289 2400841102416009588297217)
                    ·
                      refine ⟨1800630826812007191222913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400841102416009588297217 1800630826812007191222913)
                      ·
                        rfl

theorem cell23_3506716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_3506716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506716 prefixEnd_3506716 := by exact prefixLift 3506716
  have htrace : WordTrace (prefixWord ++ tailWord_3506716) baseStart_3506716 baseEnd_3506716 := by
    simpa [prefixWord, tailWord_3506716, baseEnd_3506716] using wordTrace_append hprefix tailTrace_3506716
  have hstable : (prefixWord ++ tailWord_3506716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506716).length < 2 ^ (prefixWord ++ tailWord_3506716).sum := by decide
  have hdescent : baseEnd_3506716 < baseStart_3506716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506772 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3506772 : Nat := 118140960795 + 3506772 * 2 ^ 59
def prefixEnd_3506772 : Nat := 4983230072969 + 3 ^ 40 * 3506772 * 2
def baseEnd_3506772 : Nat := 1800659581728658972122655

theorem tailTrace_3506772 : CollatzResearch.WordTrace tailWord_3506772 prefixEnd_3506772 1800659581728658972122655 := by
  unfold tailWord_3506772
  simp only [CollatzResearch.WordTrace]
  refine ⟨63951241225785713910565285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85268321634380951880753713 63951241225785713910565285)
  ·
    refine ⟨11990857729834821358230991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63951241225785713910565285 11990857729834821358230991)
    ·
      refine ⟨17986286594752232037346487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11990857729834821358230991 17986286594752232037346487)
      ·
        refine ⟨26979429892128348056019731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17986286594752232037346487 26979429892128348056019731)
        ·
          refine ⟨40469144838192522084029597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26979429892128348056019731 40469144838192522084029597)
          ·
            refine ⟨15175929314322195781511099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40469144838192522084029597 15175929314322195781511099)
            ·
              refine ⟨22763893971483293672266649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15175929314322195781511099 22763893971483293672266649)
              ·
                refine ⟨17072920478612470254199987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22763893971483293672266649 17072920478612470254199987)
                ·
                  refine ⟨25609380717918705381299981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17072920478612470254199987 25609380717918705381299981)
                  ·
                    refine ⟨9603517769219514517987493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25609380717918705381299981 9603517769219514517987493)
                    ·
                      refine ⟨1800659581728658972122655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9603517769219514517987493 1800659581728658972122655)
                      ·
                        rfl

theorem cell23_3506772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3506772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506772 prefixEnd_3506772 := by exact prefixLift 3506772
  have htrace : WordTrace (prefixWord ++ tailWord_3506772) baseStart_3506772 baseEnd_3506772 := by
    simpa [prefixWord, tailWord_3506772, baseEnd_3506772] using wordTrace_append hprefix tailTrace_3506772
  have hstable : (prefixWord ++ tailWord_3506772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506772).length < 2 ^ (prefixWord ++ tailWord_3506772).sum := by decide
  have hdescent : baseEnd_3506772 < baseStart_3506772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506806 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3506806 : Nat := 118140960795 + 3506806 * 2 ^ 59
def prefixEnd_3506806 : Nat := 4983230072969 + 3 ^ 40 * 3506806 * 2
def baseEnd_3506806 : Nat := 1800677040070911839097499

theorem tailTrace_3506806 : CollatzResearch.WordTrace tailWord_3506806 prefixEnd_3506806 1800677040070911839097499 := by
  unfold tailWord_3506806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993982658340515726741767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85269148355632167751912181 7993982658340515726741767)
  ·
    refine ⟨11990973987510773590112651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993982658340515726741767 11990973987510773590112651)
    ·
      refine ⟨17986460981266160385168977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11990973987510773590112651 17986460981266160385168977)
      ·
        refine ⟨13489845735949620288876733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17986460981266160385168977 13489845735949620288876733)
        ·
          refine ⟨5058692150981107608328775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13489845735949620288876733 5058692150981107608328775)
          ·
            refine ⟨7588038226471661412493163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058692150981107608328775 7588038226471661412493163)
            ·
              refine ⟨11382057339707492118739745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588038226471661412493163 11382057339707492118739745)
              ·
                refine ⟨8536543004780619089054809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11382057339707492118739745 8536543004780619089054809)
                ·
                  refine ⟨6402407253585464316791107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8536543004780619089054809 6402407253585464316791107)
                  ·
                    refine ⟨9603610880378196475186661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402407253585464316791107 9603610880378196475186661)
                    ·
                      refine ⟨1800677040070911839097499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9603610880378196475186661 1800677040070911839097499)
                      ·
                        rfl

theorem cell23_3506806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3506806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506806 prefixEnd_3506806 := by exact prefixLift 3506806
  have htrace : WordTrace (prefixWord ++ tailWord_3506806) baseStart_3506806 baseEnd_3506806 := by
    simpa [prefixWord, tailWord_3506806, baseEnd_3506806] using wordTrace_append hprefix tailTrace_3506806
  have hstable : (prefixWord ++ tailWord_3506806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506806).length < 2 ^ (prefixWord ++ tailWord_3506806).sum := by decide
  have hdescent : baseEnd_3506806 < baseStart_3506806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506809 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3506809 : Nat := 118140960795 + 3506809 * 2 ^ 59
def prefixEnd_3506809 : Nat := 4983230072969 + 3 ^ 40 * 3506809 * 2
def baseEnd_3506809 : Nat := 1800678580512875327359985

theorem tailTrace_3506809 : CollatzResearch.WordTrace tailWord_3506809 prefixEnd_3506809 1800678580512875327359985 := by
  unfold tailWord_3506809
  simp only [CollatzResearch.WordTrace]
  refine ⟨127903831952437383140227481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85269221301624922093484987 127903831952437383140227481)
  ·
    refine ⟨95927873964328037355170611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127903831952437383140227481 95927873964328037355170611)
    ·
      refine ⟨143891810946492056032755917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95927873964328037355170611 143891810946492056032755917)
      ·
        refine ⟨53959429104934521012283469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143891810946492056032755917 53959429104934521012283469)
        ·
          refine ⟨20234785914350445379606301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53959429104934521012283469 20234785914350445379606301)
          ·
            refine ⟨7588044717881417017352363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20234785914350445379606301 7588044717881417017352363)
            ·
              refine ⟨11382067076822125526028545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588044717881417017352363 11382067076822125526028545)
              ·
                refine ⟨8536550307616594144521409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11382067076822125526028545 8536550307616594144521409)
                ·
                  refine ⟨6402412730712445608391057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8536550307616594144521409 6402412730712445608391057)
                  ·
                    refine ⟨4801809548034334206293293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402412730712445608391057 4801809548034334206293293)
                    ·
                      refine ⟨1800678580512875327359985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801809548034334206293293 1800678580512875327359985)
                      ·
                        rfl

theorem cell23_3506809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3506809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506809 prefixEnd_3506809 := by exact prefixLift 3506809
  have htrace : WordTrace (prefixWord ++ tailWord_3506809) baseStart_3506809 baseEnd_3506809 := by
    simpa [prefixWord, tailWord_3506809, baseEnd_3506809] using wordTrace_append hprefix tailTrace_3506809
  have hstable : (prefixWord ++ tailWord_3506809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506809).length < 2 ^ (prefixWord ++ tailWord_3506809).sum := by decide
  have hdescent : baseEnd_3506809 < baseStart_3506809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506815 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3506815 : Nat := 118140960795 + 3506815 * 2 ^ 59
def prefixEnd_3506815 : Nat := 4983230072969 + 3 ^ 40 * 3506815 * 2
def baseEnd_3506815 : Nat := 1800681661396802303884957

theorem tailTrace_3506815 : CollatzResearch.WordTrace tailWord_3506815 prefixEnd_3506815 1800681661396802303884957 := by
  unfold tailWord_3506815
  simp only [CollatzResearch.WordTrace]
  refine ⟨127904050790415646164945899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85269367193610430776630599 127904050790415646164945899)
  ·
    refine ⟨191856076185623469247418849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127904050790415646164945899 191856076185623469247418849)
    ·
      refine ⟨143892057139217601935564137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191856076185623469247418849 143892057139217601935564137)
      ·
        refine ⟨107919042854413201451673103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143892057139217601935564137 107919042854413201451673103)
        ·
          refine ⟨161878564281619802177509655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107919042854413201451673103 161878564281619802177509655)
          ·
            refine ⟨242817846422429703266264483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161878564281619802177509655 242817846422429703266264483)
            ·
              refine ⟨364226769633644554899396725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242817846422429703266264483 364226769633644554899396725)
              ·
                refine ⟨34146259653154177021818443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364226769633644554899396725 34146259653154177021818443)
                ·
                  refine ⟨51219389479731265532727665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34146259653154177021818443 51219389479731265532727665)
                  ·
                    refine ⟨38414542109798449149545749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51219389479731265532727665 38414542109798449149545749)
                    ·
                      refine ⟨1800681661396802303884957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38414542109798449149545749 1800681661396802303884957)
                      ·
                        rfl

theorem cell23_3506815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3506815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506815 prefixEnd_3506815 := by exact prefixLift 3506815
  have htrace : WordTrace (prefixWord ++ tailWord_3506815) baseStart_3506815 baseEnd_3506815 := by
    simpa [prefixWord, tailWord_3506815, baseEnd_3506815] using wordTrace_append hprefix tailTrace_3506815
  have hstable : (prefixWord ++ tailWord_3506815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506815).length < 2 ^ (prefixWord ++ tailWord_3506815).sum := by decide
  have hdescent : baseEnd_3506815 < baseStart_3506815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506825 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_3506825 : Nat := 118140960795 + 3506825 * 2 ^ 59
def prefixEnd_3506825 : Nat := 4983230072969 + 3 ^ 40 * 3506825 * 2
def baseEnd_3506825 : Nat := 600228932067782421586637

theorem tailTrace_3506825 : CollatzResearch.WordTrace tailWord_3506825 prefixEnd_3506825 600228932067782421586637 := by
  unfold tailWord_3506825
  simp only [CollatzResearch.WordTrace]
  refine ⟨127904415520379417872809929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85269610346919611915206619 127904415520379417872809929)
  ·
    refine ⟨95928311640284563404607447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127904415520379417872809929 95928311640284563404607447)
    ·
      refine ⟨143892467460426845106911171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95928311640284563404607447 143892467460426845106911171)
      ·
        refine ⟨215838701190640267660366757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143892467460426845106911171 215838701190640267660366757)
        ·
          refine ⟨40469756473245050186318767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215838701190640267660366757 40469756473245050186318767)
          ·
            refine ⟨60704634709867575279478151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40469756473245050186318767 60704634709867575279478151)
            ·
              refine ⟨91056952064801362919217227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60704634709867575279478151 91056952064801362919217227)
              ·
                refine ⟨136585428097202044378825841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91056952064801362919217227 136585428097202044378825841)
                ·
                  refine ⟨102439071072901533284119381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136585428097202044378825841 102439071072901533284119381)
                  ·
                    refine ⟨600228932067782421586637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 102439071072901533284119381 600228932067782421586637)
                    ·
                      rfl

theorem cell23_3506825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_3506825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506825 prefixEnd_3506825 := by exact prefixLift 3506825
  have htrace : WordTrace (prefixWord ++ tailWord_3506825) baseStart_3506825 baseEnd_3506825 := by
    simpa [prefixWord, tailWord_3506825, baseEnd_3506825] using wordTrace_append hprefix tailTrace_3506825
  have hstable : (prefixWord ++ tailWord_3506825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506825).length < 2 ^ (prefixWord ++ tailWord_3506825).sum := by decide
  have hdescent : baseEnd_3506825 < baseStart_3506825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506835 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_3506835 : Nat := 118140960795 + 3506835 * 2 ^ 59
def prefixEnd_3506835 : Nat := 4983230072969 + 3 ^ 40 * 3506835 * 2
def baseEnd_3506835 : Nat := 1800691931009892225634865

theorem tailTrace_3506835 : CollatzResearch.WordTrace tailWord_3506835 prefixEnd_3506835 1800691931009892225634865 := by
  unfold tailWord_3506835
  simp only [CollatzResearch.WordTrace]
  refine ⟨127904780250343189580673959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85269853500228793053782639 127904780250343189580673959)
  ·
    refine ⟨191857170375514784371010939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127904780250343189580673959 191857170375514784371010939)
    ·
      refine ⟨287785755563272176556516409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191857170375514784371010939 287785755563272176556516409)
      ·
        refine ⟨215839316672454132417387307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287785755563272176556516409 215839316672454132417387307)
        ·
          refine ⟨323758975008681198626080961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215839316672454132417387307 323758975008681198626080961)
          ·
            refine ⟨242819231256510898969560721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323758975008681198626080961 242819231256510898969560721)
            ·
              refine ⟨182114423442383174227170541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242819231256510898969560721 182114423442383174227170541)
              ·
                refine ⟨68292908790893690335188953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182114423442383174227170541 68292908790893690335188953)
                ·
                  refine ⟨51219681593170267751391715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68292908790893690335188953 51219681593170267751391715)
                  ·
                    refine ⟨76829522389755401627087573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51219681593170267751391715 76829522389755401627087573)
                    ·
                      refine ⟨1800691931009892225634865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76829522389755401627087573 1800691931009892225634865)
                      ·
                        rfl

theorem cell23_3506835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_3506835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506835 prefixEnd_3506835 := by exact prefixLift 3506835
  have htrace : WordTrace (prefixWord ++ tailWord_3506835) baseStart_3506835 baseEnd_3506835 := by
    simpa [prefixWord, tailWord_3506835, baseEnd_3506835] using wordTrace_append hprefix tailTrace_3506835
  have hstable : (prefixWord ++ tailWord_3506835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506835).length < 2 ^ (prefixWord ++ tailWord_3506835).sum := by decide
  have hdescent : baseEnd_3506835 < baseStart_3506835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506839 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3506839 : Nat := 118140960795 + 3506839 * 2 ^ 59
def prefixEnd_3506839 : Nat := 4983230072969 + 3 ^ 40 * 3506839 * 2
def baseEnd_3506839 : Nat := 1800693984932510209984847

theorem tailTrace_3506839 : CollatzResearch.WordTrace tailWord_3506839 prefixEnd_3506839 1800693984932510209984847 := by
  unfold tailWord_3506839
  simp only [CollatzResearch.WordTrace]
  refine ⟨127904926142328698263819571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85269950761552465509213047 127904926142328698263819571)
  ·
    refine ⟨191857389213493047395729357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127904926142328698263819571 191857389213493047395729357)
    ·
      refine ⟨71946520955059892773398509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191857389213493047395729357 71946520955059892773398509)
      ·
        refine ⟨26979945358147459790024441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71946520955059892773398509 26979945358147459790024441)
        ·
          refine ⟨20234959018610594842518331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26979945358147459790024441 20234959018610594842518331)
          ·
            refine ⟨30352438527915892263777497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20234959018610594842518331 30352438527915892263777497)
            ·
              refine ⟨22764328895936919197833123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30352438527915892263777497 22764328895936919197833123)
              ·
                refine ⟨34146493343905378796749685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22764328895936919197833123 34146493343905378796749685)
                ·
                  refine ⟨3201233750991129262195283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34146493343905378796749685 3201233750991129262195283)
                  ·
                    refine ⟨4801850626486693893292925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3201233750991129262195283 4801850626486693893292925)
                    ·
                      refine ⟨1800693984932510209984847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801850626486693893292925 1800693984932510209984847)
                      ·
                        rfl

theorem cell23_3506839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3506839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506839 prefixEnd_3506839 := by exact prefixLift 3506839
  have htrace : WordTrace (prefixWord ++ tailWord_3506839) baseStart_3506839 baseEnd_3506839 := by
    simpa [prefixWord, tailWord_3506839, baseEnd_3506839] using wordTrace_append hprefix tailTrace_3506839
  have hstable : (prefixWord ++ tailWord_3506839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506839).length < 2 ^ (prefixWord ++ tailWord_3506839).sum := by decide
  have hdescent : baseEnd_3506839 < baseStart_3506839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506900 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3506900 : Nat := 118140960795 + 3506900 * 2 ^ 59
def prefixEnd_3506900 : Nat := 4983230072969 + 3 ^ 40 * 3506900 * 2
def baseEnd_3506900 : Nat := 1800725307252434471322067

theorem tailTrace_3506900 : CollatzResearch.WordTrace tailWord_3506900 prefixEnd_3506900 1800725307252434471322067 := by
  unfold tailWord_3506900
  simp only [CollatzResearch.WordTrace]
  refine ⟨63953575497553852840895077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85271433996738470454526769 63953575497553852840895077)
  ·
    refine ⟨11991295405791347407667827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63953575497553852840895077 11991295405791347407667827)
    ·
      refine ⟨17986943108687021111501741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991295405791347407667827 17986943108687021111501741)
      ·
        refine ⟨6745103665757632916813153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17986943108687021111501741 6745103665757632916813153)
        ·
          refine ⟨5058827749318224687609865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6745103665757632916813153 5058827749318224687609865)
          ·
            refine ⟨3794120811988668515707399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5058827749318224687609865 3794120811988668515707399)
            ·
              refine ⟨5691181217983002773561099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794120811988668515707399 5691181217983002773561099)
              ·
                refine ⟨8536771826974504160341649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691181217983002773561099 8536771826974504160341649)
                ·
                  refine ⟨6402578870230878120256237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8536771826974504160341649 6402578870230878120256237)
                  ·
                    refine ⟨2400967076336579295096089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6402578870230878120256237 2400967076336579295096089)
                    ·
                      refine ⟨1800725307252434471322067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400967076336579295096089 1800725307252434471322067)
                      ·
                        rfl

theorem cell23_3506900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3506900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506900 prefixEnd_3506900 := by exact prefixLift 3506900
  have htrace : WordTrace (prefixWord ++ tailWord_3506900) baseStart_3506900 baseEnd_3506900 := by
    simpa [prefixWord, tailWord_3506900, baseEnd_3506900] using wordTrace_append hprefix tailTrace_3506900
  have hstable : (prefixWord ++ tailWord_3506900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506900).length < 2 ^ (prefixWord ++ tailWord_3506900).sum := by decide
  have hdescent : baseEnd_3506900 < baseStart_3506900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506913 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_3506913 : Nat := 118140960795 + 3506913 * 2 ^ 59
def prefixEnd_3506913 : Nat := 4983230072969 + 3 ^ 40 * 3506913 * 2
def baseEnd_3506913 : Nat := 1800731982500942920459507

theorem tailTrace_3506913 : CollatzResearch.WordTrace tailWord_3506913 prefixEnd_3506913 1800731982500942920459507 := by
  unfold tailWord_3506913
  simp only [CollatzResearch.WordTrace]
  refine ⟨127907625144060608902013393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85271750096040405934675595 127907625144060608902013393)
  ·
    refine ⟨95930718858045456676510045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127907625144060608902013393 95930718858045456676510045)
    ·
      refine ⟨35974019571767046253691267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95930718858045456676510045 35974019571767046253691267)
      ·
        refine ⟨53961029357650569380536901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35974019571767046253691267 53961029357650569380536901)
        ·
          refine ⟨10117693004559481758850669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53961029357650569380536901 10117693004559481758850669)
          ·
            refine ⟨3794134876709805659569001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10117693004559481758850669 3794134876709805659569001)
            ·
              refine ⟨2845601157532354244676751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794134876709805659569001 2845601157532354244676751)
              ·
                refine ⟨4268401736298531367015127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845601157532354244676751 4268401736298531367015127)
                ·
                  refine ⟨6402602604447797050522691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268401736298531367015127 6402602604447797050522691)
                  ·
                    refine ⟨9603903906671695575784037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402602604447797050522691 9603903906671695575784037)
                    ·
                      refine ⟨1800731982500942920459507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9603903906671695575784037 1800731982500942920459507)
                      ·
                        rfl

theorem cell23_3506913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_3506913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506913 prefixEnd_3506913 := by exact prefixLift 3506913
  have htrace : WordTrace (prefixWord ++ tailWord_3506913) baseStart_3506913 baseEnd_3506913 := by
    simpa [prefixWord, tailWord_3506913, baseEnd_3506913] using wordTrace_append hprefix tailTrace_3506913
  have hstable : (prefixWord ++ tailWord_3506913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506913).length < 2 ^ (prefixWord ++ tailWord_3506913).sum := by decide
  have hdescent : baseEnd_3506913 < baseStart_3506913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506916 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_3506916 : Nat := 118140960795 + 3506916 * 2 ^ 59
def prefixEnd_3506916 : Nat := 4983230072969 + 3 ^ 40 * 3506916 * 2
def baseEnd_3506916 : Nat := 1800733522942906408721993

theorem tailTrace_3506916 : CollatzResearch.WordTrace tailWord_3506916 prefixEnd_3506916 1800733522942906408721993 := by
  unfold tailWord_3506916
  simp only [CollatzResearch.WordTrace]
  refine ⟨63953867281524870207186301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85271823042033160276248401 63953867281524870207186301)
  ·
    refine ⟨23982700230571826327694863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63953867281524870207186301 23982700230571826327694863)
    ·
      refine ⟨35974050345857739491542295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23982700230571826327694863 35974050345857739491542295)
      ·
        refine ⟨53961075518786609237313443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35974050345857739491542295 53961075518786609237313443)
        ·
          refine ⟨80941613278179913855970165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53961075518786609237313443 80941613278179913855970165)
          ·
            refine ⟨7588276244829366923997203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80941613278179913855970165 7588276244829366923997203)
            ·
              refine ⟨11382414367244050385995805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588276244829366923997203 11382414367244050385995805)
              ·
                refine ⟨4268405387716518894748427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382414367244050385995805 4268405387716518894748427)
                ·
                  refine ⟨6402608081574778342122641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268405387716518894748427 6402608081574778342122641)
                  ·
                    refine ⟨4801956061181083756591981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402608081574778342122641 4801956061181083756591981)
                    ·
                      refine ⟨1800733522942906408721993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801956061181083756591981 1800733522942906408721993)
                      ·
                        rfl

theorem cell23_3506916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_3506916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506916 prefixEnd_3506916 := by exact prefixLift 3506916
  have htrace : WordTrace (prefixWord ++ tailWord_3506916) baseStart_3506916 baseEnd_3506916 := by
    simpa [prefixWord, tailWord_3506916, baseEnd_3506916] using wordTrace_append hprefix tailTrace_3506916
  have hstable : (prefixWord ++ tailWord_3506916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506916).length < 2 ^ (prefixWord ++ tailWord_3506916).sum := by decide
  have hdescent : baseEnd_3506916 < baseStart_3506916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506922 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_3506922 : Nat := 118140960795 + 3506922 * 2 ^ 59
def prefixEnd_3506922 : Nat := 4983230072969 + 3 ^ 40 * 3506922 * 2
def baseEnd_3506922 : Nat := 1800736603826833385246965

theorem tailTrace_3506922 : CollatzResearch.WordTrace tailWord_3506922 prefixEnd_3506922 1800736603826833385246965 := by
  unfold tailWord_3506922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31976988350257000859772755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85271968934018668959394013 31976988350257000859772755)
  ·
    refine ⟨47965482525385501289659133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31976988350257000859772755 47965482525385501289659133)
    ·
      refine ⟨17987055947019562983622175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47965482525385501289659133 17987055947019562983622175)
      ·
        refine ⟨26980583920529344475433263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987055947019562983622175 26980583920529344475433263)
        ·
          refine ⟨40470875880794016713149895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26980583920529344475433263 40470875880794016713149895)
          ·
            refine ⟨60706313821191025069724843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40470875880794016713149895 60706313821191025069724843)
            ·
              refine ⟨91059470731786537604587265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60706313821191025069724843 91059470731786537604587265)
              ·
                refine ⟨68294603048839903203440449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91059470731786537604587265 68294603048839903203440449)
                ·
                  refine ⟨51220952286629927402580337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68294603048839903203440449 51220952286629927402580337)
                  ·
                    refine ⟨38415714214972445551935253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51220952286629927402580337 38415714214972445551935253)
                    ·
                      refine ⟨1800736603826833385246965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38415714214972445551935253 1800736603826833385246965)
                      ·
                        rfl

theorem cell23_3506922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_3506922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506922 prefixEnd_3506922 := by exact prefixLift 3506922
  have htrace : WordTrace (prefixWord ++ tailWord_3506922) baseStart_3506922 baseEnd_3506922 := by
    simpa [prefixWord, tailWord_3506922, baseEnd_3506922] using wordTrace_append hprefix tailTrace_3506922
  have hstable : (prefixWord ++ tailWord_3506922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506922).length < 2 ^ (prefixWord ++ tailWord_3506922).sum := by decide
  have hdescent : baseEnd_3506922 < baseStart_3506922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506930 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_3506930 : Nat := 118140960795 + 3506930 * 2 ^ 59
def prefixEnd_3506930 : Nat := 4983230072969 + 3 ^ 40 * 3506930 * 2
def baseEnd_3506930 : Nat := 1800740711672069353946929

theorem tailTrace_3506930 : CollatzResearch.WordTrace tailWord_3506930 prefixEnd_3506930 1800740711672069353946929 := by
  unfold tailWord_3506930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31977061296249755201345561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85272163456666013870254829 31977061296249755201345561)
  ·
    refine ⟨23982795972187316401009171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31977061296249755201345561 23982795972187316401009171)
    ·
      refine ⟨35974193958280974601513757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23982795972187316401009171 35974193958280974601513757)
      ·
        refine ⟨13490322734355365475567659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35974193958280974601513757 13490322734355365475567659)
        ·
          refine ⟨20235484101533048213351489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13490322734355365475567659 20235484101533048213351489)
          ·
            refine ⟨15176613076149786160013617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20235484101533048213351489 15176613076149786160013617)
            ·
              refine ⟨11382459807112339620010213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15176613076149786160013617 11382459807112339620010213)
              ·
                refine ⟨2134211213833563678751915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11382459807112339620010213 2134211213833563678751915)
                ·
                  refine ⟨3201316820750345518127873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134211213833563678751915 3201316820750345518127873)
                  ·
                    refine ⟨2400987615562759138595905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3201316820750345518127873 2400987615562759138595905)
                    ·
                      refine ⟨1800740711672069353946929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400987615562759138595905 1800740711672069353946929)
                      ·
                        rfl

theorem cell23_3506930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_3506930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506930 prefixEnd_3506930 := by exact prefixLift 3506930
  have htrace : WordTrace (prefixWord ++ tailWord_3506930) baseStart_3506930 baseEnd_3506930 := by
    simpa [prefixWord, tailWord_3506930, baseEnd_3506930] using wordTrace_append hprefix tailTrace_3506930
  have hstable : (prefixWord ++ tailWord_3506930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506930).length < 2 ^ (prefixWord ++ tailWord_3506930).sum := by decide
  have hdescent : baseEnd_3506930 < baseStart_3506930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507026 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_3507026 : Nat := 118140960795 + 3507026 * 2 ^ 59
def prefixEnd_3507026 : Nat := 4983230072969 + 3 ^ 40 * 3507026 * 2
def baseEnd_3507026 : Nat := 200087778423877886482943

theorem tailTrace_3507026 : CollatzResearch.WordTrace tailWord_3507026 prefixEnd_3507026 200087778423877886482943 := by
  unfold tailWord_3507026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31977936648162807300219233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85274497728434152800584621 31977936648162807300219233)
  ·
    refine ⟨23983452486122105475164425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31977936648162807300219233 23983452486122105475164425)
    ·
      refine ⟨17987589364591579106373319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23983452486122105475164425 17987589364591579106373319)
      ·
        refine ⟨26981384046887368659559979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987589364591579106373319 26981384046887368659559979)
        ·
          refine ⟨40472076070331052989339969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26981384046887368659559979 40472076070331052989339969)
          ·
            refine ⟨30354057052748289742004977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40472076070331052989339969 30354057052748289742004977)
            ·
              refine ⟨22765542789561217306503733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30354057052748289742004977 22765542789561217306503733)
              ·
                refine ⟨2134269636521364122484725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22765542789561217306503733 2134269636521364122484725)
                ·
                  refine ⟨200087778423877886482943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134269636521364122484725 200087778423877886482943)
                  ·
                    rfl

theorem cell23_3507026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_3507026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507026 prefixEnd_3507026 := by exact prefixLift 3507026
  have htrace : WordTrace (prefixWord ++ tailWord_3507026) baseStart_3507026 baseEnd_3507026 := by
    simpa [prefixWord, tailWord_3507026, baseEnd_3507026] using wordTrace_append hprefix tailTrace_3507026
  have hstable : (prefixWord ++ tailWord_3507026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507026).length < 2 ^ (prefixWord ++ tailWord_3507026).sum := by decide
  have hdescent : baseEnd_3507026 < baseStart_3507026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507039 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 2, 5]
def baseStart_3507039 : Nat := 118140960795 + 3507039 * 2 ^ 59
def prefixEnd_3507039 : Nat := 4983230072969 + 3 ^ 40 * 3507039 * 2
def baseEnd_3507039 : Nat := 600265560354469809161309

theorem tailTrace_3507039 : CollatzResearch.WordTrace tailWord_3507039 prefixEnd_3507039 600265560354469809161309 := by
  unfold tailWord_3507039
  simp only [CollatzResearch.WordTrace]
  refine ⟨127912220741604132421100171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85274813827736088280733447 127912220741604132421100171)
  ·
    refine ⟨191868331112406198631650257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127912220741604132421100171 191868331112406198631650257)
    ·
      refine ⟨143901248334304648973737693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191868331112406198631650257 143901248334304648973737693)
      ·
        refine ⟨53962968125364243365151635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143901248334304648973737693 53962968125364243365151635)
        ·
          refine ⟨80944452188046365047727453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53962968125364243365151635 80944452188046365047727453)
          ·
            refine ⟨30354169570517386892897795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80944452188046365047727453 30354169570517386892897795)
            ·
              refine ⟨45531254355776080339346693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30354169570517386892897795 45531254355776080339346693)
              ·
                refine ⟨8537110191708015063627505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45531254355776080339346693 8537110191708015063627505)
                ·
                  refine ⟨6402832643781011297720629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8537110191708015063627505 6402832643781011297720629)
                  ·
                    refine ⟨600265560354469809161309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6402832643781011297720629 600265560354469809161309)
                    ·
                      rfl

theorem cell23_3507039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_3507039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507039 prefixEnd_3507039 := by exact prefixLift 3507039
  have htrace : WordTrace (prefixWord ++ tailWord_3507039) baseStart_3507039 baseEnd_3507039 := by
    simpa [prefixWord, tailWord_3507039, baseEnd_3507039] using wordTrace_append hprefix tailTrace_3507039
  have hstable : (prefixWord ++ tailWord_3507039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507039).length < 2 ^ (prefixWord ++ tailWord_3507039).sum := by decide
  have hdescent : baseEnd_3507039 < baseStart_3507039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507043 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 5]
def baseStart_3507043 : Nat := 118140960795 + 3507043 * 2 ^ 59
def prefixEnd_3507043 : Nat := 4983230072969 + 3 ^ 40 * 3507043 * 2
def baseEnd_3507043 : Nat := 200088748331780823537101

theorem tailTrace_3507043 : CollatzResearch.WordTrace tailWord_3507043 prefixEnd_3507043 200088748331780823537101 := by
  unfold tailWord_3507043
  simp only [CollatzResearch.WordTrace]
  refine ⟨127912366633589641104245783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85274911089059760736163855 127912366633589641104245783)
  ·
    refine ⟨191868549950384461656368675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127912366633589641104245783 191868549950384461656368675)
    ·
      refine ⟨287802824925576692484553013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191868549950384461656368675 287802824925576692484553013)
      ·
        refine ⟨26981514836772814920426845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287802824925576692484553013 26981514836772814920426845)
        ·
          refine ⟨10118068063789805595160067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26981514836772814920426845 10118068063789805595160067)
          ·
            refine ⟨15177102095684708392740101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118068063789805595160067 15177102095684708392740101)
            ·
              refine ⟨2845706642940882823638769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15177102095684708392740101 2845706642940882823638769)
              ·
                refine ⟨2134279982205662117729077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845706642940882823638769 2134279982205662117729077)
                ·
                  refine ⟨200088748331780823537101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134279982205662117729077 200088748331780823537101)
                  ·
                    rfl

theorem cell23_3507043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 5].length) (baseStart_3507043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507043 prefixEnd_3507043 := by exact prefixLift 3507043
  have htrace : WordTrace (prefixWord ++ tailWord_3507043) baseStart_3507043 baseEnd_3507043 := by
    simpa [prefixWord, tailWord_3507043, baseEnd_3507043] using wordTrace_append hprefix tailTrace_3507043
  have hstable : (prefixWord ++ tailWord_3507043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507043).length < 2 ^ (prefixWord ++ tailWord_3507043).sum := by decide
  have hdescent : baseEnd_3507043 < baseStart_3507043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507059 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4]
def baseStart_3507059 : Nat := 118140960795 + 3507059 * 2 ^ 59
def prefixEnd_3507059 : Nat := 4983230072969 + 3 ^ 40 * 3507059 * 2
def baseEnd_3507059 : Nat := 1800806950676499349233835

theorem tailTrace_3507059 : CollatzResearch.WordTrace tailWord_3507059 prefixEnd_3507059 1800806950676499349233835 := by
  unfold tailWord_3507059
  simp only [CollatzResearch.WordTrace]
  refine ⟨127912950201531675836828231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85275300134354450557885487 127912950201531675836828231)
  ·
    refine ⟨191869425302297513755242347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127912950201531675836828231 191869425302297513755242347)
    ·
      refine ⟨287804137953446270632863521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191869425302297513755242347 287804137953446270632863521)
      ·
        refine ⟨215853103465084702974647641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287804137953446270632863521 215853103465084702974647641)
        ·
          refine ⟨161889827598813527230985731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215853103465084702974647641 161889827598813527230985731)
          ·
            refine ⟨242834741398220290846478597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161889827598813527230985731 242834741398220290846478597)
            ·
              refine ⟨45531514012166304533714737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242834741398220290846478597 45531514012166304533714737)
              ·
                refine ⟨34148635509124728400286053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45531514012166304533714737 34148635509124728400286053)
                ·
                  refine ⟨6402869157960886575053635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34148635509124728400286053 6402869157960886575053635)
                  ·
                    refine ⟨9604303736941329862580453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402869157960886575053635 9604303736941329862580453)
                    ·
                      refine ⟨1800806950676499349233835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9604303736941329862580453 1800806950676499349233835)
                      ·
                        rfl

theorem cell23_3507059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_3507059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507059 prefixEnd_3507059 := by exact prefixLift 3507059
  have htrace : WordTrace (prefixWord ++ tailWord_3507059) baseStart_3507059 baseEnd_3507059 := by
    simpa [prefixWord, tailWord_3507059, baseEnd_3507059] using wordTrace_append hprefix tailTrace_3507059
  have hstable : (prefixWord ++ tailWord_3507059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507059).length < 2 ^ (prefixWord ++ tailWord_3507059).sum := by decide
  have hdescent : baseEnd_3507059 < baseStart_3507059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507076 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_3507076 : Nat := 118140960795 + 3507076 * 2 ^ 59
def prefixEnd_3507076 : Nat := 4983230072969 + 3 ^ 40 * 3507076 * 2
def baseEnd_3507076 : Nat := 1800815679847625782721257

theorem tailTrace_3507076 : CollatzResearch.WordTrace tailWord_3507076 prefixEnd_3507076 1800815679847625782721257 := by
  unfold tailWord_3507076
  simp only [CollatzResearch.WordTrace]
  refine ⟨63956785121235043870098541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85275713494980058493464721 63956785121235043870098541)
  ·
    refine ⟨23983794420463141451286953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63956785121235043870098541 23983794420463141451286953)
    ·
      refine ⟨17987845815347356088465215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23983794420463141451286953 17987845815347356088465215)
      ·
        refine ⟨26981768723021034132697823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987845815347356088465215 26981768723021034132697823)
        ·
          refine ⟨40472653084531551199046735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26981768723021034132697823 40472653084531551199046735)
          ·
            refine ⟨60708979626797326798570103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40472653084531551199046735 60708979626797326798570103)
            ·
              refine ⟨91063469440195990197855155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60708979626797326798570103 91063469440195990197855155)
              ·
                refine ⟨136595204160293985296782733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91063469440195990197855155 136595204160293985296782733)
                ·
                  refine ⟨51223201560110244486293525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136595204160293985296782733 51223201560110244486293525)
                  ·
                    refine ⟨2401087573130167710295009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51223201560110244486293525 2401087573130167710295009)
                    ·
                      refine ⟨1800815679847625782721257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401087573130167710295009 1800815679847625782721257)
                      ·
                        rfl

theorem cell23_3507076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_3507076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507076 prefixEnd_3507076 := by exact prefixLift 3507076
  have htrace : WordTrace (prefixWord ++ tailWord_3507076) baseStart_3507076 baseEnd_3507076 := by
    simpa [prefixWord, tailWord_3507076, baseEnd_3507076] using wordTrace_append hprefix tailTrace_3507076
  have hstable : (prefixWord ++ tailWord_3507076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507076).length < 2 ^ (prefixWord ++ tailWord_3507076).sum := by decide
  have hdescent : baseEnd_3507076 < baseStart_3507076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507103 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 3, 4]
def baseStart_3507103 : Nat := 118140960795 + 3507103 * 2 ^ 59
def prefixEnd_3507103 : Nat := 4983230072969 + 3 ^ 40 * 3507103 * 2
def baseEnd_3507103 : Nat := 600276514608432392361211

theorem tailTrace_3507103 : CollatzResearch.WordTrace tailWord_3507103 prefixEnd_3507103 600276514608432392361211 := by
  unfold tailWord_3507103
  simp only [CollatzResearch.WordTrace]
  refine ⟨127914555013372271351429963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85276370008914847567619975 127914555013372271351429963)
  ·
    refine ⟨191871832520058407027144945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127914555013372271351429963 191871832520058407027144945)
    ·
      refine ⟨143903874390043805270358709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191871832520058407027144945 143903874390043805270358709)
      ·
        refine ⟨13490988224066606744096129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143903874390043805270358709 13490988224066606744096129)
        ·
          refine ⟨10118241168049955058072097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13490988224066606744096129 10118241168049955058072097)
          ·
            refine ⟨7588680876037466293554073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10118241168049955058072097 7588680876037466293554073)
            ·
              refine ⟨5691510657028099720165555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7588680876037466293554073 5691510657028099720165555)
              ·
                refine ⟨8537265985542149580248333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691510657028099720165555 8537265985542149580248333)
                ·
                  refine ⟨3201474744578306092593125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8537265985542149580248333 3201474744578306092593125)
                  ·
                    refine ⟨600276514608432392361211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3201474744578306092593125 600276514608432392361211)
                    ·
                      rfl

theorem cell23_3507103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_3507103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507103 prefixEnd_3507103 := by exact prefixLift 3507103
  have htrace : WordTrace (prefixWord ++ tailWord_3507103) baseStart_3507103 baseEnd_3507103 := by
    simpa [prefixWord, tailWord_3507103, baseEnd_3507103] using wordTrace_append hprefix tailTrace_3507103
  have hstable : (prefixWord ++ tailWord_3507103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507103).length < 2 ^ (prefixWord ++ tailWord_3507103).sum := by decide
  have hdescent : baseEnd_3507103 < baseStart_3507103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507153 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_3507153 : Nat := 118140960795 + 3507153 * 2 ^ 59
def prefixEnd_3507153 : Nat := 4983230072969 + 3 ^ 40 * 3507153 * 2
def baseEnd_3507153 : Nat := 1800855217858021981458403

theorem tailTrace_3507153 : CollatzResearch.WordTrace tailWord_3507153 prefixEnd_3507153 1800855217858021981458403 := by
  unfold tailWord_3507153
  simp only [CollatzResearch.WordTrace]
  refine ⟨127916378663191129890750113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85277585775460753260500075 127916378663191129890750113)
  ·
    refine ⟨95937283997393347418062585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127916378663191129890750113 95937283997393347418062585)
    ·
      refine ⟨71952962998045010563546939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95937283997393347418062585 71952962998045010563546939)
      ·
        refine ⟨107929444497067515845320409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71952962998045010563546939 107929444497067515845320409)
        ·
          refine ⟨80947083372800636883990307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107929444497067515845320409 80947083372800636883990307)
          ·
            refine ⟨121420625059200955325985461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80947083372800636883990307 121420625059200955325985461)
            ·
              refine ⟨11383183599300089561811137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121420625059200955325985461 11383183599300089561811137)
              ·
                refine ⟨8537387699475067171358353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11383183599300089561811137 8537387699475067171358353)
                ·
                  refine ⟨6403040774606300378518765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8537387699475067171358353 6403040774606300378518765)
                  ·
                    refine ⟨2401140290477362641944537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6403040774606300378518765 2401140290477362641944537)
                    ·
                      refine ⟨1800855217858021981458403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401140290477362641944537 1800855217858021981458403)
                      ·
                        rfl

theorem cell23_3507153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_3507153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507153 prefixEnd_3507153 := by exact prefixLift 3507153
  have htrace : WordTrace (prefixWord ++ tailWord_3507153) baseStart_3507153 baseEnd_3507153 := by
    simpa [prefixWord, tailWord_3507153, baseEnd_3507153] using wordTrace_append hprefix tailTrace_3507153
  have hstable : (prefixWord ++ tailWord_3507153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507153).length < 2 ^ (prefixWord ++ tailWord_3507153).sum := by decide
  have hdescent : baseEnd_3507153 < baseStart_3507153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507159 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 5, 6]
def baseStart_3507159 : Nat := 118140960795 + 3507159 * 2 ^ 59
def prefixEnd_3507159 : Nat := 4983230072969 + 3 ^ 40 * 3507159 * 2
def baseEnd_3507159 : Nat := 600286099580649652661125

theorem tailTrace_3507159 : CollatzResearch.WordTrace tailWord_3507159 prefixEnd_3507159 600286099580649652661125 := by
  unfold tailWord_3507159
  simp only [CollatzResearch.WordTrace]
  refine ⟨127916597501169392915468531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85277731667446261943645687 127916597501169392915468531)
  ·
    refine ⟨191874896251754089373202797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127916597501169392915468531 191874896251754089373202797)
    ·
      refine ⟨71953086094407783514951049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191874896251754089373202797 71953086094407783514951049)
      ·
        refine ⟨53964814570805837636213287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71953086094407783514951049 53964814570805837636213287)
        ·
          refine ⟨80947221856208756454319931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53964814570805837636213287 80947221856208756454319931)
          ·
            refine ⟨121420832784313134681479897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80947221856208756454319931 121420832784313134681479897)
            ·
              refine ⟨91065624588234851011109923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121420832784313134681479897 91065624588234851011109923)
              ·
                refine ⟨136598436882352276516664885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91065624588234851011109923 136598436882352276516664885)
                ·
                  refine ⟨12806103457720525923437333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136598436882352276516664885 12806103457720525923437333)
                  ·
                    refine ⟨600286099580649652661125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12806103457720525923437333 600286099580649652661125)
                    ·
                      rfl

theorem cell23_3507159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_3507159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507159 prefixEnd_3507159 := by exact prefixLift 3507159
  have htrace : WordTrace (prefixWord ++ tailWord_3507159) baseStart_3507159 baseEnd_3507159 := by
    simpa [prefixWord, tailWord_3507159, baseEnd_3507159] using wordTrace_append hprefix tailTrace_3507159
  have hstable : (prefixWord ++ tailWord_3507159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507159).length < 2 ^ (prefixWord ++ tailWord_3507159).sum := by decide
  have hdescent : baseEnd_3507159 < baseStart_3507159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507160 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_3507160 : Nat := 118140960795 + 3507160 * 2 ^ 59
def prefixEnd_3507160 : Nat := 4983230072969 + 3 ^ 40 * 3507160 * 2
def baseEnd_3507160 : Nat := 1800858812222603454070871

theorem tailTrace_3507160 : CollatzResearch.WordTrace tailWord_3507160 prefixEnd_3507160 1800858812222603454070871 := by
  unfold tailWord_3507160
  simp only [CollatzResearch.WordTrace]
  refine ⟨63958316987082885043127467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85277755982777180057503289 63958316987082885043127467)
  ·
    refine ⟨95937475480624327564691201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63958316987082885043127467 95937475480624327564691201)
    ·
      refine ⟨71953106610468245673518401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95937475480624327564691201 71953106610468245673518401)
      ·
        refine ⟨53964829957851184255138801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71953106610468245673518401 53964829957851184255138801)
        ·
          refine ⟨40473622468388388191354101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53964829957851184255138801 40473622468388388191354101)
          ·
            refine ⟨3794402106411411392939447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40473622468388388191354101 3794402106411411392939447)
            ·
              refine ⟨5691603159617117089409171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794402106411411392939447 5691603159617117089409171)
              ·
                refine ⟨8537404739425675634113757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691603159617117089409171 8537404739425675634113757)
                ·
                  refine ⟨3201526777284628362792659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8537404739425675634113757 3201526777284628362792659)
                  ·
                    refine ⟨4802290165926942544188989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3201526777284628362792659 4802290165926942544188989)
                    ·
                      refine ⟨1800858812222603454070871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802290165926942544188989 1800858812222603454070871)
                      ·
                        rfl

theorem cell23_3507160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_3507160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507160 prefixEnd_3507160 := by exact prefixLift 3507160
  have htrace : WordTrace (prefixWord ++ tailWord_3507160) baseStart_3507160 baseEnd_3507160 := by
    simpa [prefixWord, tailWord_3507160, baseEnd_3507160] using wordTrace_append hprefix tailTrace_3507160
  have hstable : (prefixWord ++ tailWord_3507160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507160).length < 2 ^ (prefixWord ++ tailWord_3507160).sum := by decide
  have hdescent : baseEnd_3507160 < baseStart_3507160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507183 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_3507183 : Nat := 118140960795 + 3507183 * 2 ^ 59
def prefixEnd_3507183 : Nat := 4983230072969 + 3 ^ 40 * 3507183 * 2
def baseEnd_3507183 : Nat := 1800870622277656864083265

theorem tailTrace_3507183 : CollatzResearch.WordTrace tailWord_3507183 prefixEnd_3507183 1800870622277656864083265 := by
  unfold tailWord_3507183
  simp only [CollatzResearch.WordTrace]
  refine ⟨127917472853082445014342203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85278315235388296676228135 127917472853082445014342203)
  ·
    refine ⟨191876209279623667521513305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127917472853082445014342203 191876209279623667521513305)
    ·
      refine ⟨143907156959717750641134979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191876209279623667521513305 143907156959717750641134979)
      ·
        refine ⟨215860735439576625961702469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143907156959717750641134979 215860735439576625961702469)
        ·
          refine ⟨40473887894920617367819213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215860735439576625961702469 40473887894920617367819213)
          ·
            refine ⟨15177707960595231512932205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40473887894920617367819213 15177707960595231512932205)
            ·
              refine ⟨5691640485223211817349577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15177707960595231512932205 5691640485223211817349577)
              ·
                refine ⟨4268730363917408863012183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691640485223211817349577 4268730363917408863012183)
                ·
                  refine ⟨6403095545876113294518275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268730363917408863012183 6403095545876113294518275)
                  ·
                    refine ⟨9604643318814169941777413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6403095545876113294518275 9604643318814169941777413)
                    ·
                      refine ⟨1800870622277656864083265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9604643318814169941777413 1800870622277656864083265)
                      ·
                        rfl

theorem cell23_3507183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_3507183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507183 prefixEnd_3507183 := by exact prefixLift 3507183
  have htrace : WordTrace (prefixWord ++ tailWord_3507183) baseStart_3507183 baseEnd_3507183 := by
    simpa [prefixWord, tailWord_3507183, baseEnd_3507183] using wordTrace_append hprefix tailTrace_3507183
  have hstable : (prefixWord ++ tailWord_3507183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507183).length < 2 ^ (prefixWord ++ tailWord_3507183).sum := by decide
  have hdescent : baseEnd_3507183 < baseStart_3507183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507196 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3507196 : Nat := 118140960795 + 3507196 * 2 ^ 59
def prefixEnd_3507196 : Nat := 4983230072969 + 3 ^ 40 * 3507196 * 2
def baseEnd_3507196 : Nat := 1800877297526165313220705

theorem tailTrace_3507196 : CollatzResearch.WordTrace tailWord_3507196 prefixEnd_3507196 1800877297526165313220705 := by
  unfold tailWord_3507196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63958973501017674117282721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85278631334690232156376961 63958973501017674117282721)
  ·
    refine ⟨47969230125763255587962041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63958973501017674117282721 47969230125763255587962041)
    ·
      refine ⟨35976922594322441690971531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47969230125763255587962041 35976922594322441690971531)
      ·
        refine ⟨53965383891483662536457297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35976922594322441690971531 53965383891483662536457297)
        ·
          refine ⟨40474037918612746902342973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53965383891483662536457297 40474037918612746902342973)
          ·
            refine ⟨15177764219479780088378615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40474037918612746902342973 15177764219479780088378615)
            ·
              refine ⟨22766646329219670132567923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15177764219479780088378615 22766646329219670132567923)
              ·
                refine ⟨34149969493829505198851885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22766646329219670132567923 34149969493829505198851885)
                ·
                  refine ⟨12806238560186064449569457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34149969493829505198851885 12806238560186064449569457)
                  ·
                    refine ⟨9604678920139548337177093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12806238560186064449569457 9604678920139548337177093)
                    ·
                      refine ⟨1800877297526165313220705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9604678920139548337177093 1800877297526165313220705)
                      ·
                        rfl

theorem cell23_3507196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3507196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507196 prefixEnd_3507196 := by exact prefixLift 3507196
  have htrace : WordTrace (prefixWord ++ tailWord_3507196) baseStart_3507196 baseEnd_3507196 := by
    simpa [prefixWord, tailWord_3507196, baseEnd_3507196] using wordTrace_append hprefix tailTrace_3507196
  have hstable : (prefixWord ++ tailWord_3507196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507196).length < 2 ^ (prefixWord ++ tailWord_3507196).sum := by decide
  have hdescent : baseEnd_3507196 < baseStart_3507196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507210 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_3507210 : Nat := 118140960795 + 3507210 * 2 ^ 59
def prefixEnd_3507210 : Nat := 4983230072969 + 3 ^ 40 * 3507210 * 2
def baseEnd_3507210 : Nat := 600294828751776086148547

theorem tailTrace_3507210 : CollatzResearch.WordTrace tailWord_3507210 prefixEnd_3507210 600294828751776086148547 := by
  unfold tailWord_3507210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31979614405996157156393771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85278971749323085750383389 31979614405996157156393771)
  ·
    refine ⟨47969421608994235734590657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31979614405996157156393771 47969421608994235734590657)
    ·
      refine ⟨35977066206745676800942993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47969421608994235734590657 35977066206745676800942993)
      ·
        refine ⟨26982799655059257600707245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35977066206745676800942993 26982799655059257600707245)
        ·
          refine ⟨10118549870647221600265217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26982799655059257600707245 10118549870647221600265217)
          ·
            refine ⟨7588912402985416200198913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10118549870647221600265217 7588912402985416200198913)
            ·
              refine ⟨5691684302239062150149185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7588912402985416200198913 5691684302239062150149185)
              ·
                refine ⟨4268763226679296612611889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691684302239062150149185 4268763226679296612611889)
                ·
                  refine ⟨3201572420009472459458917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4268763226679296612611889 3201572420009472459458917)
                  ·
                    refine ⟨600294828751776086148547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3201572420009472459458917 600294828751776086148547)
                    ·
                      rfl

theorem cell23_3507210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_3507210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507210 prefixEnd_3507210 := by exact prefixLift 3507210
  have htrace : WordTrace (prefixWord ++ tailWord_3507210) baseStart_3507210 baseEnd_3507210 := by
    simpa [prefixWord, tailWord_3507210, baseEnd_3507210] using wordTrace_append hprefix tailTrace_3507210
  have hstable : (prefixWord ++ tailWord_3507210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507210).length < 2 ^ (prefixWord ++ tailWord_3507210).sum := by decide
  have hdescent : baseEnd_3507210 < baseStart_3507210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507223 : List Nat := [1, 1, 3, 5, 1, 3, 1, 8]
def baseStart_3507223 : Nat := 118140960795 + 3507223 * 2 ^ 59
def prefixEnd_3507223 : Nat := 4983230072969 + 3 ^ 40 * 3507223 * 2
def baseEnd_3507223 : Nat := 66699672648290248429003

theorem tailTrace_3507223 : CollatzResearch.WordTrace tailWord_3507223 prefixEnd_3507223 66699672648290248429003 := by
  unfold tailWord_3507223
  simp only [CollatzResearch.WordTrace]
  refine ⟨127918931772937531845798323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85279287848625021230532215 127918931772937531845798323)
  ·
    refine ⟨191878397659406297768697485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127918931772937531845798323 191878397659406297768697485)
    ·
      refine ⟨71954399122277361663261557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191878397659406297768697485 71954399122277361663261557)
      ·
        refine ⟨6745724917713502655930771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71954399122277361663261557 6745724917713502655930771)
        ·
          refine ⟨10118587376570253983896157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745724917713502655930771 10118587376570253983896157)
          ·
            refine ⟨3794470266213845243961059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10118587376570253983896157 3794470266213845243961059)
            ·
              refine ⟨5691705399320767865941589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794470266213845243961059 5691705399320767865941589)
              ·
                refine ⟨66699672648290248429003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5691705399320767865941589 66699672648290248429003)
                ·
                  rfl

theorem cell23_3507223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 8].length) (baseStart_3507223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507223 prefixEnd_3507223 := by exact prefixLift 3507223
  have htrace : WordTrace (prefixWord ++ tailWord_3507223) baseStart_3507223 baseEnd_3507223 := by
    simpa [prefixWord, tailWord_3507223, baseEnd_3507223] using wordTrace_append hprefix tailTrace_3507223
  have hstable : (prefixWord ++ tailWord_3507223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507223).length < 2 ^ (prefixWord ++ tailWord_3507223).sum := by decide
  have hdescent : baseEnd_3507223 < baseStart_3507223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507233 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3507233 : Nat := 118140960795 + 3507233 * 2 ^ 59
def prefixEnd_3507233 : Nat := 4983230072969 + 3 ^ 40 * 3507233 * 2
def baseEnd_3507233 : Nat := 1800896296310381668458035

theorem tailTrace_3507233 : CollatzResearch.WordTrace tailWord_3507233 prefixEnd_3507233 1800896296310381668458035 := by
  unfold tailWord_3507233
  simp only [CollatzResearch.WordTrace]
  refine ⟨127919296502901303553662353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85279531001934202369108235 127919296502901303553662353)
  ·
    refine ⟨95939472377175977665246765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127919296502901303553662353 95939472377175977665246765)
    ·
      refine ⟨35977302141440991624467537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95939472377175977665246765 35977302141440991624467537)
      ·
        refine ⟨26982976606080743718350653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35977302141440991624467537 26982976606080743718350653)
        ·
          refine ⟨10118616227280278894381495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26982976606080743718350653 10118616227280278894381495)
          ·
            refine ⟨15177924340920418341572243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118616227280278894381495 15177924340920418341572243)
            ·
              refine ⟨22766886511380627512358365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15177924340920418341572243 22766886511380627512358365)
              ·
                refine ⟨8537582441767735317134387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22766886511380627512358365 8537582441767735317134387)
                ·
                  refine ⟨12806373662651602975701581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8537582441767735317134387 12806373662651602975701581)
                  ·
                    refine ⟨4802390123494351115888093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12806373662651602975701581 4802390123494351115888093)
                    ·
                      refine ⟨1800896296310381668458035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802390123494351115888093 1800896296310381668458035)
                      ·
                        rfl

theorem cell23_3507233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3507233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507233 prefixEnd_3507233 := by exact prefixLift 3507233
  have htrace : WordTrace (prefixWord ++ tailWord_3507233) baseStart_3507233 baseEnd_3507233 := by
    simpa [prefixWord, tailWord_3507233, baseEnd_3507233] using wordTrace_append hprefix tailTrace_3507233
  have hstable : (prefixWord ++ tailWord_3507233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507233).length < 2 ^ (prefixWord ++ tailWord_3507233).sum := by decide
  have hdescent : baseEnd_3507233 < baseStart_3507233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507243 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 3, 3, 2]
def baseStart_3507243 : Nat := 118140960795 + 3507243 * 2 ^ 59
def prefixEnd_3507243 : Nat := 4983230072969 + 3 ^ 40 * 3507243 * 2
def baseEnd_3507243 : Nat := 1800901431116926629332989

theorem tailTrace_3507243 : CollatzResearch.WordTrace tailWord_3507243 prefixEnd_3507243 1800901431116926629332989 := by
  unfold tailWord_3507243
  simp only [CollatzResearch.WordTrace]
  refine ⟨127919661232865075261526383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85279774155243383507684255 127919661232865075261526383)
  ·
    refine ⟨191879491849297612892289575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127919661232865075261526383 191879491849297612892289575)
    ·
      refine ⟨287819237773946419338434363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191879491849297612892289575 287819237773946419338434363)
      ·
        refine ⟨431728856660919629007651545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287819237773946419338434363 431728856660919629007651545)
        ·
          refine ⟨323796642495689721755738659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431728856660919629007651545 323796642495689721755738659)
          ·
            refine ⟨485694963743534582633607989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323796642495689721755738659 485694963743534582633607989)
            ·
              refine ⟨45533902850956367121900749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485694963743534582633607989 45533902850956367121900749)
              ·
                refine ⟨17075213569108637670712781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45533902850956367121900749 17075213569108637670712781)
                ·
                  refine ⟨6403205088415739126517293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17075213569108637670712781 6403205088415739126517293)
                  ·
                    refine ⟨2401201908155902172443985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6403205088415739126517293 2401201908155902172443985)
                    ·
                      refine ⟨1800901431116926629332989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401201908155902172443985 1800901431116926629332989)
                      ·
                        rfl

theorem cell23_3507243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 3, 2].length) (baseStart_3507243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507243 prefixEnd_3507243 := by exact prefixLift 3507243
  have htrace : WordTrace (prefixWord ++ tailWord_3507243) baseStart_3507243 baseEnd_3507243 := by
    simpa [prefixWord, tailWord_3507243, baseEnd_3507243] using wordTrace_append hprefix tailTrace_3507243
  have hstable : (prefixWord ++ tailWord_3507243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507243).length < 2 ^ (prefixWord ++ tailWord_3507243).sum := by decide
  have hdescent : baseEnd_3507243 < baseStart_3507243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507254 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3507254 : Nat := 118140960795 + 3507254 * 2 ^ 59
def prefixEnd_3507254 : Nat := 4983230072969 + 3 ^ 40 * 3507254 * 2
def baseEnd_3507254 : Nat := 1800907079404126086295439

theorem tailTrace_3507254 : CollatzResearch.WordTrace tailWord_3507254 prefixEnd_3507254 1800907079404126086295439 := by
  unfold tailWord_3507254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995003902239076508761051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85280041623883482760117877 7995003902239076508761051)
  ·
    refine ⟨11992505853358614763141577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7995003902239076508761051 11992505853358614763141577)
    ·
      refine ⟨8994379390018961072356183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11992505853358614763141577 8994379390018961072356183)
      ·
        refine ⟨13491569085028441608534275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8994379390018961072356183 13491569085028441608534275)
        ·
          refine ⟨20237353627542662412801413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13491569085028441608534275 20237353627542662412801413)
          ·
            refine ⟨3794503805164249202400265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20237353627542662412801413 3794503805164249202400265)
            ·
              refine ⟨2845877853873186901800199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794503805164249202400265 2845877853873186901800199)
              ·
                refine ⟨4268816780809780352700299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845877853873186901800199 4268816780809780352700299)
                ·
                  refine ⟨6403225171214670529050449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268816780809780352700299 6403225171214670529050449)
                  ·
                    refine ⟨4802418878411002896787837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403225171214670529050449 4802418878411002896787837)
                    ·
                      refine ⟨1800907079404126086295439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802418878411002896787837 1800907079404126086295439)
                      ·
                        rfl

theorem cell23_3507254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3507254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507254 prefixEnd_3507254 := by exact prefixLift 3507254
  have htrace : WordTrace (prefixWord ++ tailWord_3507254) baseStart_3507254 baseEnd_3507254 := by
    simpa [prefixWord, tailWord_3507254, baseEnd_3507254] using wordTrace_append hprefix tailTrace_3507254
  have hstable : (prefixWord ++ tailWord_3507254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507254).length < 2 ^ (prefixWord ++ tailWord_3507254).sum := by decide
  have hdescent : baseEnd_3507254 < baseStart_3507254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507276 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3507276 : Nat := 118140960795 + 3507276 * 2 ^ 59
def prefixEnd_3507276 : Nat := 4983230072969 + 3 ^ 40 * 3507276 * 2
def baseEnd_3507276 : Nat := 1800918375978525000220337

theorem tailTrace_3507276 : CollatzResearch.WordTrace tailWord_3507276 prefixEnd_3507276 1800918375978525000220337 := by
  unfold tailWord_3507276
  simp only [CollatzResearch.WordTrace]
  refine ⟨63960432420872760948738841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85280576561163681264985121 63960432420872760948738841)
  ·
    refine ⟨47970324315654570711554131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63960432420872760948738841 47970324315654570711554131)
    ·
      refine ⟨71955486473481856067331197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47970324315654570711554131 71955486473481856067331197)
      ·
        refine ⟨26983307427555696025249199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71955486473481856067331197 26983307427555696025249199)
        ·
          refine ⟨40474961141333544037873799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26983307427555696025249199 40474961141333544037873799)
          ·
            refine ⟨60712441712000316056810699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40474961141333544037873799 60712441712000316056810699)
            ·
              refine ⟨91068662568000474085216049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60712441712000316056810699 91068662568000474085216049)
              ·
                refine ⟨68301496926000355563912037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91068662568000474085216049 68301496926000355563912037)
                ·
                  refine ⟨12806530673625066668233507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68301496926000355563912037 12806530673625066668233507)
                  ·
                    refine ⟨19209796010437600002350261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12806530673625066668233507 19209796010437600002350261)
                    ·
                      refine ⟨1800918375978525000220337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19209796010437600002350261 1800918375978525000220337)
                      ·
                        rfl

theorem cell23_3507276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3507276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507276 prefixEnd_3507276 := by exact prefixLift 3507276
  have htrace : WordTrace (prefixWord ++ tailWord_3507276) baseStart_3507276 baseEnd_3507276 := by
    simpa [prefixWord, tailWord_3507276, baseEnd_3507276] using wordTrace_append hprefix tailTrace_3507276
  have hstable : (prefixWord ++ tailWord_3507276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507276).length < 2 ^ (prefixWord ++ tailWord_3507276).sum := by decide
  have hdescent : baseEnd_3507276 < baseStart_3507276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507296 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 7]
def baseStart_3507296 : Nat := 118140960795 + 3507296 * 2 ^ 59
def prefixEnd_3507296 : Nat := 4983230072969 + 3 ^ 40 * 3507296 * 2
def baseEnd_3507296 : Nat := 200103182843512769107805

theorem tailTrace_3507296 : CollatzResearch.WordTrace tailWord_3507296 prefixEnd_3507296 200103182843512769107805 := by
  unfold tailWord_3507296
  simp only [CollatzResearch.WordTrace]
  refine ⟨63960797150836532656602871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85281062867782043542137161 63960797150836532656602871)
  ·
    refine ⟨95941195726254798984904307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63960797150836532656602871 95941195726254798984904307)
    ·
      refine ⟨143911793589382198477356461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95941195726254798984904307 143911793589382198477356461)
      ·
        refine ⟨53966922596018324429008673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143911793589382198477356461 53966922596018324429008673)
        ·
          refine ⟨40475191947013743321756505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53966922596018324429008673 40475191947013743321756505)
          ·
            refine ⟨30356393960260307491317379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40475191947013743321756505 30356393960260307491317379)
            ·
              refine ⟨45534590940390461236976069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30356393960260307491317379 45534590940390461236976069)
              ·
                refine ⟨8537735801323211481933013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45534590940390461236976069 8537735801323211481933013)
                ·
                  refine ⟨200103182843512769107805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8537735801323211481933013 200103182843512769107805)
                  ·
                    rfl

theorem cell23_3507296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_3507296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507296 prefixEnd_3507296 := by exact prefixLift 3507296
  have htrace : WordTrace (prefixWord ++ tailWord_3507296) baseStart_3507296 baseEnd_3507296 := by
    simpa [prefixWord, tailWord_3507296, baseEnd_3507296] using wordTrace_append hprefix tailTrace_3507296
  have hstable : (prefixWord ++ tailWord_3507296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507296).length < 2 ^ (prefixWord ++ tailWord_3507296).sum := by decide
  have hdescent : baseEnd_3507296 < baseStart_3507296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507313 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 5]
def baseStart_3507313 : Nat := 118140960795 + 3507313 * 2 ^ 59
def prefixEnd_3507313 : Nat := 4983230072969 + 3 ^ 40 * 3507313 * 2
def baseEnd_3507313 : Nat := 200104152751415706161963

theorem tailTrace_3507313 : CollatzResearch.WordTrace tailWord_3507313 prefixEnd_3507313 200104152751415706161963 := by
  unfold tailWord_3507313
  simp only [CollatzResearch.WordTrace]
  refine ⟨127922214342611477216574593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85281476228407651477716395 127922214342611477216574593)
  ·
    refine ⟨95941660756958607912430945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127922214342611477216574593 95941660756958607912430945)
    ·
      refine ⟨71956245567718955934323209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95941660756958607912430945 71956245567718955934323209)
      ·
        refine ⟨53967184175789216950742407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71956245567718955934323209 53967184175789216950742407)
        ·
          refine ⟨80950776263683825426113611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53967184175789216950742407 80950776263683825426113611)
          ·
            refine ⟨121426164395525738139170417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80950776263683825426113611 121426164395525738139170417)
            ·
              refine ⟨91069623296644303604377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121426164395525738139170417 91069623296644303604377813)
              ·
                refine ⟨2134444296015100865727605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91069623296644303604377813 2134444296015100865727605)
                ·
                  refine ⟨200104152751415706161963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134444296015100865727605 200104152751415706161963)
                  ·
                    rfl

theorem cell23_3507313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 5].length) (baseStart_3507313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507313 prefixEnd_3507313 := by exact prefixLift 3507313
  have htrace : WordTrace (prefixWord ++ tailWord_3507313) baseStart_3507313 baseEnd_3507313 := by
    simpa [prefixWord, tailWord_3507313, baseEnd_3507313] using wordTrace_append hprefix tailTrace_3507313
  have hstable : (prefixWord ++ tailWord_3507313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507313).length < 2 ^ (prefixWord ++ tailWord_3507313).sum := by decide
  have hdescent : baseEnd_3507313 < baseStart_3507313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507370 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3507370 : Nat := 118140960795 + 3507370 * 2 ^ 59
def prefixEnd_3507370 : Nat := 4983230072969 + 3 ^ 40 * 3507370 * 2
def baseEnd_3507370 : Nat := 1800966643160047632444905

theorem tailTrace_3507370 : CollatzResearch.WordTrace tailWord_3507370 prefixEnd_3507370 1800966643160047632444905 := by
  unfold tailWord_3507370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31981073325851243987849891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85282862202269983967599709 31981073325851243987849891)
  ·
    refine ⟨47971609988776865981774837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31981073325851243987849891 47971609988776865981774837)
    ·
      refine ⟨4497338436447831185791391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47971609988776865981774837 4497338436447831185791391)
      ·
        refine ⟨6746007654671746778687087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497338436447831185791391 6746007654671746778687087)
        ·
          refine ⟨10119011482007620168030631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746007654671746778687087 10119011482007620168030631)
          ·
            refine ⟨15178517223011430252045947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119011482007620168030631 15178517223011430252045947)
            ·
              refine ⟨22767775834517145378068921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15178517223011430252045947 22767775834517145378068921)
              ·
                refine ⟨17075831875887859033551691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22767775834517145378068921 17075831875887859033551691)
                ·
                  refine ⟨25613747813831788550327537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17075831875887859033551691 25613747813831788550327537)
                  ·
                    refine ⟨19210310860373841412745653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25613747813831788550327537 19210310860373841412745653)
                    ·
                      refine ⟨1800966643160047632444905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19210310860373841412745653 1800966643160047632444905)
                      ·
                        rfl

theorem cell23_3507370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3507370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507370 prefixEnd_3507370 := by exact prefixLift 3507370
  have htrace : WordTrace (prefixWord ++ tailWord_3507370) baseStart_3507370 baseEnd_3507370 := by
    simpa [prefixWord, tailWord_3507370, baseEnd_3507370] using wordTrace_append hprefix tailTrace_3507370
  have hstable : (prefixWord ++ tailWord_3507370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507370).length < 2 ^ (prefixWord ++ tailWord_3507370).sum := by decide
  have hdescent : baseEnd_3507370 < baseStart_3507370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507376 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_3507376 : Nat := 118140960795 + 3507376 * 2 ^ 59
def prefixEnd_3507376 : Nat := 4983230072969 + 3 ^ 40 * 3507376 * 2
def baseEnd_3507376 : Nat := 1800969724043974608969877

theorem tailTrace_3507376 : CollatzResearch.WordTrace tailWord_3507376 prefixEnd_3507376 1800969724043974608969877 := by
  unfold tailWord_3507376
  simp only [CollatzResearch.WordTrace]
  refine ⟨63962256070691619488058991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85283008094255492650745321 63962256070691619488058991)
  ·
    refine ⟨95943384106037429232088487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63962256070691619488058991 95943384106037429232088487)
    ·
      refine ⟨143915076159056143848132731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95943384106037429232088487 143915076159056143848132731)
      ·
        refine ⟨215872614238584215772199097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143915076159056143848132731 215872614238584215772199097)
        ·
          refine ⟨161904460678938161829149323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215872614238584215772199097 161904460678938161829149323)
          ·
            refine ⟨242856691018407242743723985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161904460678938161829149323 242856691018407242743723985)
            ·
              refine ⟨182142518263805432057792989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242856691018407242743723985 182142518263805432057792989)
              ·
                refine ⟨68303444348927037021672371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182142518263805432057792989 68303444348927037021672371)
                ·
                  refine ⟨102455166523390555532508557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68303444348927037021672371 102455166523390555532508557)
                  ·
                    refine ⟨38420687446271458324690709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102455166523390555532508557 38420687446271458324690709)
                    ·
                      refine ⟨1800969724043974608969877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38420687446271458324690709 1800969724043974608969877)
                      ·
                        rfl

theorem cell23_3507376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_3507376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507376 prefixEnd_3507376 := by exact prefixLift 3507376
  have htrace : WordTrace (prefixWord ++ tailWord_3507376) baseStart_3507376 baseEnd_3507376 := by
    simpa [prefixWord, tailWord_3507376, baseEnd_3507376] using wordTrace_append hprefix tailTrace_3507376
  have hstable : (prefixWord ++ tailWord_3507376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507376).length < 2 ^ (prefixWord ++ tailWord_3507376).sum := by decide
  have hdescent : baseEnd_3507376 < baseStart_3507376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507437 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3507437 : Nat := 118140960795 + 3507437 * 2 ^ 59
def prefixEnd_3507437 : Nat := 4983230072969 + 3 ^ 40 * 3507437 * 2
def baseEnd_3507437 : Nat := 200111227373766541145233

theorem tailTrace_3507437 : CollatzResearch.WordTrace tailWord_3507437 prefixEnd_3507437 200111227373766541145233 := by
  unfold tailWord_3507437
  simp only [CollatzResearch.WordTrace]
  refine ⟨127926736994162246394088565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85284491329441497596059043 127926736994162246394088565)
  ·
    refine ⟨11993131593202710599445803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127926736994162246394088565 11993131593202710599445803)
    ·
      refine ⟨17989697389804065899168705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11993131593202710599445803 17989697389804065899168705)
      ·
        refine ⟨13492273042353049424376529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17989697389804065899168705 13492273042353049424376529)
        ·
          refine ⟨10119204781764787068282397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13492273042353049424376529 10119204781764787068282397)
          ·
            refine ⟨3794701793161795150605899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10119204781764787068282397 3794701793161795150605899)
            ·
              refine ⟨5692052689742692725908849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794701793161795150605899 5692052689742692725908849)
              ·
                refine ⟨4269039517307019544431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692052689742692725908849 4269039517307019544431637)
                ·
                  refine ⟨200111227373766541145233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4269039517307019544431637 200111227373766541145233)
                  ·
                    rfl

theorem cell23_3507437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3507437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507437 prefixEnd_3507437 := by exact prefixLift 3507437
  have htrace : WordTrace (prefixWord ++ tailWord_3507437) baseStart_3507437 baseEnd_3507437 := by
    simpa [prefixWord, tailWord_3507437, baseEnd_3507437] using wordTrace_append hprefix tailTrace_3507437
  have hstable : (prefixWord ++ tailWord_3507437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507437).length < 2 ^ (prefixWord ++ tailWord_3507437).sum := by decide
  have hdescent : baseEnd_3507437 < baseStart_3507437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507473 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3507473 : Nat := 118140960795 + 3507473 * 2 ^ 59
def prefixEnd_3507473 : Nat := 4983230072969 + 3 ^ 40 * 3507473 * 2
def baseEnd_3507473 : Nat := 1801019531667460729456931

theorem tailTrace_3507473 : CollatzResearch.WordTrace tailWord_3507473 prefixEnd_3507473 1801019531667460729456931 := by
  unfold tailWord_3507473
  simp only [CollatzResearch.WordTrace]
  refine ⟨127928050022031824542399073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85285366681354549694932715 127928050022031824542399073)
  ·
    refine ⟨95946037516523868406799305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127928050022031824542399073 95946037516523868406799305)
    ·
      refine ⟨71959528137392901305099479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95946037516523868406799305 71959528137392901305099479)
      ·
        refine ⟨107939292206089351957649219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71959528137392901305099479 107939292206089351957649219)
        ·
          refine ⟨161908938309134027936473829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107939292206089351957649219 161908938309134027936473829)
          ·
            refine ⟨30357925932962630238088843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161908938309134027936473829 30357925932962630238088843)
            ·
              refine ⟨45536888899443945357133265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30357925932962630238088843 45536888899443945357133265)
              ·
                refine ⟨34152666674582959017849949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45536888899443945357133265 34152666674582959017849949)
                ·
                  refine ⟨12807250002968609631693731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34152666674582959017849949 12807250002968609631693731)
                  ·
                    refine ⟨19210875004452914447540597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12807250002968609631693731 19210875004452914447540597)
                    ·
                      refine ⟨1801019531667460729456931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19210875004452914447540597 1801019531667460729456931)
                      ·
                        rfl

theorem cell23_3507473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3507473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507473 prefixEnd_3507473 := by exact prefixLift 3507473
  have htrace : WordTrace (prefixWord ++ tailWord_3507473) baseStart_3507473 baseEnd_3507473 := by
    simpa [prefixWord, tailWord_3507473, baseEnd_3507473] using wordTrace_append hprefix tailTrace_3507473
  have hstable : (prefixWord ++ tailWord_3507473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507473).length < 2 ^ (prefixWord ++ tailWord_3507473).sum := by decide
  have hdescent : baseEnd_3507473 < baseStart_3507473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507480 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 4, 4]
def baseStart_3507480 : Nat := 118140960795 + 3507480 * 2 ^ 59
def prefixEnd_3507480 : Nat := 4983230072969 + 3 ^ 40 * 3507480 * 2
def baseEnd_3507480 : Nat := 600341042010680734023133

theorem tailTrace_3507480 : CollatzResearch.WordTrace tailWord_3507480 prefixEnd_3507480 600341042010680734023133 := by
  unfold tailWord_3507480
  simp only [CollatzResearch.WordTrace]
  refine ⟨63964152666503232368951947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85285536888670976491935929 63964152666503232368951947)
  ·
    refine ⟨95946228999754848553427921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63964152666503232368951947 95946228999754848553427921)
    ·
      refine ⟨71959671749816136415070941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95946228999754848553427921 71959671749816136415070941)
      ·
        refine ⟨26984876906181051155651603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71959671749816136415070941 26984876906181051155651603)
        ·
          refine ⟨40477315359271576733477405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26984876906181051155651603 40477315359271576733477405)
          ·
            refine ⟨15178993259726841275054027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40477315359271576733477405 15178993259726841275054027)
            ·
              refine ⟨22768489889590261912581041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15178993259726841275054027 22768489889590261912581041)
              ·
                refine ⟨17076367417192696434435781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22768489889590261912581041 17076367417192696434435781)
                ·
                  refine ⟨3201818890723630581456709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17076367417192696434435781 3201818890723630581456709)
                  ·
                    refine ⟨600341042010680734023133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3201818890723630581456709 600341042010680734023133)
                    ·
                      rfl

theorem cell23_3507480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_3507480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507480 prefixEnd_3507480 := by exact prefixLift 3507480
  have htrace : WordTrace (prefixWord ++ tailWord_3507480) baseStart_3507480 baseEnd_3507480 := by
    simpa [prefixWord, tailWord_3507480, baseEnd_3507480] using wordTrace_append hprefix tailTrace_3507480
  have hstable : (prefixWord ++ tailWord_3507480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507480).length < 2 ^ (prefixWord ++ tailWord_3507480).sum := by decide
  have hdescent : baseEnd_3507480 < baseStart_3507480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507483 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_3507483 : Nat := 118140960795 + 3507483 * 2 ^ 59
def prefixEnd_3507483 : Nat := 4983230072969 + 3 ^ 40 * 3507483 * 2
def baseEnd_3507483 : Nat := 1801024666474005690331885

theorem tailTrace_3507483 : CollatzResearch.WordTrace tailWord_3507483 prefixEnd_3507483 1801024666474005690331885 := by
  unfold tailWord_3507483
  simp only [CollatzResearch.WordTrace]
  refine ⟨127928414751995596250263103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85285609834663730833508735 127928414751995596250263103)
  ·
    refine ⟨191892622127993394375394655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127928414751995596250263103 191892622127993394375394655)
    ·
      refine ⟨287838933191990091563091983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191892622127993394375394655 287838933191990091563091983)
      ·
        refine ⟨431758399787985137344637975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287838933191990091563091983 431758399787985137344637975)
        ·
          refine ⟨647637599681977706016956963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431758399787985137344637975 647637599681977706016956963)
          ·
            refine ⟨971456399522966559025435445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647637599681977706016956963 971456399522966559025435445)
            ·
              refine ⟨91074037455278114908634573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 971456399522966559025435445 91074037455278114908634573)
              ·
                refine ⟨34152764045729293090737965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91074037455278114908634573 34152764045729293090737965)
                ·
                  refine ⟨12807286517148484909026737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34152764045729293090737965 12807286517148484909026737)
                  ·
                    refine ⟨9605464887861363681770053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12807286517148484909026737 9605464887861363681770053)
                    ·
                      refine ⟨1801024666474005690331885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9605464887861363681770053 1801024666474005690331885)
                      ·
                        rfl

theorem cell23_3507483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_3507483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507483 prefixEnd_3507483 := by exact prefixLift 3507483
  have htrace : WordTrace (prefixWord ++ tailWord_3507483) baseStart_3507483 baseEnd_3507483 := by
    simpa [prefixWord, tailWord_3507483, baseEnd_3507483] using wordTrace_append hprefix tailTrace_3507483
  have hstable : (prefixWord ++ tailWord_3507483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507483).length < 2 ^ (prefixWord ++ tailWord_3507483).sum := by decide
  have hdescent : baseEnd_3507483 < baseStart_3507483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507493 : List Nat := [1, 3, 1, 2, 4, 1, 11]
def baseStart_3507493 : Nat := 118140960795 + 3507493 * 2 ^ 59
def prefixEnd_3507493 : Nat := 4983230072969 + 3 ^ 40 * 3507493 * 2
def baseEnd_3507493 : Nat := 22234935818278403101319

theorem tailTrace_3507493 : CollatzResearch.WordTrace tailWord_3507493 prefixEnd_3507493 22234935818278403101319 := by
  unfold tailWord_3507493
  simp only [CollatzResearch.WordTrace]
  refine ⟨127928779481959367958127133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85285852987972911972084755 127928779481959367958127133)
  ·
    refine ⟨47973292305734762984297675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127928779481959367958127133 47973292305734762984297675)
    ·
      refine ⟨71959938458602144476446513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47973292305734762984297675 71959938458602144476446513)
      ·
        refine ⟨53969953843951608357334885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71959938458602144476446513 53969953843951608357334885)
        ·
          refine ⟨10119366345740926567000291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53969953843951608357334885 10119366345740926567000291)
          ·
            refine ⟨15179049518611389850500437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119366345740926567000291 15179049518611389850500437)
            ·
              refine ⟨22234935818278403101319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15179049518611389850500437 22234935818278403101319)
              ·
                rfl

theorem cell23_3507493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 11].length) (baseStart_3507493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507493 prefixEnd_3507493 := by exact prefixLift 3507493
  have htrace : WordTrace (prefixWord ++ tailWord_3507493) baseStart_3507493 baseEnd_3507493 := by
    simpa [prefixWord, tailWord_3507493, baseEnd_3507493] using wordTrace_append hprefix tailTrace_3507493
  have hstable : (prefixWord ++ tailWord_3507493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507493).length < 2 ^ (prefixWord ++ tailWord_3507493).sum := by decide
  have hdescent : baseEnd_3507493 < baseStart_3507493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507498 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3507498 : Nat := 118140960795 + 3507498 * 2 ^ 59
def prefixEnd_3507498 : Nat := 4983230072969 + 3 ^ 40 * 3507498 * 2
def baseEnd_3507498 : Nat := 1801032368683823131644317

theorem tailTrace_3507498 : CollatzResearch.WordTrace tailWord_3507498 prefixEnd_3507498 1801032368683823131644317 := by
  unfold tailWord_3507498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31982240461735313453014787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85285974564627502541372765 31982240461735313453014787)
  ·
    refine ⟨47973360692602970179522181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31982240461735313453014787 47973360692602970179522181)
    ·
      refine ⟨8995005129863056908660409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47973360692602970179522181 8995005129863056908660409)
      ·
        refine ⟨6746253847397292681495307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995005129863056908660409 6746253847397292681495307)
        ·
          refine ⟨10119380771095939022242961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746253847397292681495307 10119380771095939022242961)
          ·
            refine ⟨7589535578321954266682221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119380771095939022242961 7589535578321954266682221)
            ·
              refine ⟨2846075841870732850005833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7589535578321954266682221 2846075841870732850005833)
              ·
                refine ⟨2134556881403049637504375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846075841870732850005833 2134556881403049637504375)
                ·
                  refine ⟨3201835322104574456256563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134556881403049637504375 3201835322104574456256563)
                  ·
                    refine ⟨4802752983156861684384845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3201835322104574456256563 4802752983156861684384845)
                    ·
                      refine ⟨1801032368683823131644317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802752983156861684384845 1801032368683823131644317)
                      ·
                        rfl

theorem cell23_3507498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3507498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507498 prefixEnd_3507498 := by exact prefixLift 3507498
  have htrace : WordTrace (prefixWord ++ tailWord_3507498) baseStart_3507498 baseEnd_3507498 := by
    simpa [prefixWord, tailWord_3507498, baseEnd_3507498] using wordTrace_append hprefix tailTrace_3507498
  have hstable : (prefixWord ++ tailWord_3507498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507498).length < 2 ^ (prefixWord ++ tailWord_3507498).sum := by decide
  have hdescent : baseEnd_3507498 < baseStart_3507498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507520 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_3507520 : Nat := 118140960795 + 3507520 * 2 ^ 59
def prefixEnd_3507520 : Nat := 4983230072969 + 3 ^ 40 * 3507520 * 2
def baseEnd_3507520 : Nat := 1801043665258222045569215

theorem tailTrace_3507520 : CollatzResearch.WordTrace tailWord_3507520 prefixEnd_3507520 1801043665258222045569215 := by
  unfold tailWord_3507520
  simp only [CollatzResearch.WordTrace]
  refine ⟨63964882126430775784680007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85286509501907701046240009 63964882126430775784680007)
  ·
    refine ⟨95947323189646163677020011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63964882126430775784680007 95947323189646163677020011)
    ·
      refine ⟨143920984784469245515530017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95947323189646163677020011 143920984784469245515530017)
      ·
        refine ⟨107940738588351934136647513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143920984784469245515530017 107940738588351934136647513)
        ·
          refine ⟨80955553941263950602485635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107940738588351934136647513 80955553941263950602485635)
          ·
            refine ⟨121433330911895925903728453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80955553941263950602485635 121433330911895925903728453)
            ·
              refine ⟨22768749545980486106949085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121433330911895925903728453 22768749545980486106949085)
              ·
                refine ⟨8538281079742682290105907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22768749545980486106949085 8538281079742682290105907)
                ·
                  refine ⟨12807421619614023435158861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538281079742682290105907 12807421619614023435158861)
                  ·
                    refine ⟨4802783107355258788184573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12807421619614023435158861 4802783107355258788184573)
                    ·
                      refine ⟨1801043665258222045569215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802783107355258788184573 1801043665258222045569215)
                      ·
                        rfl

theorem cell23_3507520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_3507520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507520 prefixEnd_3507520 := by exact prefixLift 3507520
  have htrace : WordTrace (prefixWord ++ tailWord_3507520) baseStart_3507520 baseEnd_3507520 := by
    simpa [prefixWord, tailWord_3507520, baseEnd_3507520] using wordTrace_append hprefix tailTrace_3507520
  have hstable : (prefixWord ++ tailWord_3507520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507520).length < 2 ^ (prefixWord ++ tailWord_3507520).sum := by decide
  have hdescent : baseEnd_3507520 < baseStart_3507520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507524 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3507524 : Nat := 118140960795 + 3507524 * 2 ^ 59
def prefixEnd_3507524 : Nat := 4983230072969 + 3 ^ 40 * 3507524 * 2
def baseEnd_3507524 : Nat := 1801045719180840029919197

theorem tailTrace_3507524 : CollatzResearch.WordTrace tailWord_3507524 prefixEnd_3507524 1801045719180840029919197 := by
  unfold tailWord_3507524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63964955072423530126252813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85286606763231373501670417 63964955072423530126252813)
  ·
    refine ⟨23986858152158823797344805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63964955072423530126252813 23986858152158823797344805)
    ·
      refine ⟨4497535903529779462002151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23986858152158823797344805 4497535903529779462002151)
      ·
        refine ⟨6746303855294669193003227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497535903529779462002151 6746303855294669193003227)
        ·
          refine ⟨10119455782942003789504841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746303855294669193003227 10119455782942003789504841)
          ·
            refine ⟨7589591837206502842128631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119455782942003789504841 7589591837206502842128631)
            ·
              refine ⟨11384387755809754263192947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589591837206502842128631 11384387755809754263192947)
              ·
                refine ⟨17076581633714631394789421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384387755809754263192947 17076581633714631394789421)
                ·
                  refine ⟨6403718112642986773046033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17076581633714631394789421 6403718112642986773046033)
                  ·
                    refine ⟨4802788584482240079784525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403718112642986773046033 4802788584482240079784525)
                    ·
                      refine ⟨1801045719180840029919197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802788584482240079784525 1801045719180840029919197)
                      ·
                        rfl

theorem cell23_3507524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3507524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507524 prefixEnd_3507524 := by exact prefixLift 3507524
  have htrace : WordTrace (prefixWord ++ tailWord_3507524) baseStart_3507524 baseEnd_3507524 := by
    simpa [prefixWord, tailWord_3507524, baseEnd_3507524] using wordTrace_append hprefix tailTrace_3507524
  have hstable : (prefixWord ++ tailWord_3507524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507524).length < 2 ^ (prefixWord ++ tailWord_3507524).sum := by decide
  have hdescent : baseEnd_3507524 < baseStart_3507524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507549 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3507549 : Nat := 118140960795 + 3507549 * 2 ^ 59
def prefixEnd_3507549 : Nat := 4983230072969 + 3 ^ 40 * 3507549 * 2
def baseEnd_3507549 : Nat := 1801058556197202432106583

theorem tailTrace_3507549 : CollatzResearch.WordTrace tailWord_3507549 prefixEnd_3507549 1801058556197202432106583 := by
  unfold tailWord_3507549
  simp only [CollatzResearch.WordTrace]
  refine ⟨127930821969756489522165701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85287214646504326348110467 127930821969756489522165701)
  ·
    refine ⟨23987029119329341785406069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127930821969756489522165701 23987029119329341785406069)
    ·
      refine ⟨2248783979937125792381819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23987029119329341785406069 2248783979937125792381819)
      ·
        refine ⟨3373175969905688688572729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248783979937125792381819 3373175969905688688572729)
        ·
          refine ⟨2529881977429266516429547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3373175969905688688572729 2529881977429266516429547)
          ·
            refine ⟨3794822966143899774644321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529881977429266516429547 3794822966143899774644321)
            ·
              refine ⟨2846117224607924830983241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794822966143899774644321 2846117224607924830983241)
              ·
                refine ⟨2134587918455943623237431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846117224607924830983241 2134587918455943623237431)
                ·
                  refine ⟨3201881877683915434856147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134587918455943623237431 3201881877683915434856147)
                  ·
                    refine ⟨4802822816525873152284221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3201881877683915434856147 4802822816525873152284221)
                    ·
                      refine ⟨1801058556197202432106583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802822816525873152284221 1801058556197202432106583)
                      ·
                        rfl

theorem cell23_3507549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3507549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507549 prefixEnd_3507549 := by exact prefixLift 3507549
  have htrace : WordTrace (prefixWord ++ tailWord_3507549) baseStart_3507549 baseEnd_3507549 := by
    simpa [prefixWord, tailWord_3507549, baseEnd_3507549] using wordTrace_append hprefix tailTrace_3507549
  have hstable : (prefixWord ++ tailWord_3507549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507549).length < 2 ^ (prefixWord ++ tailWord_3507549).sum := by decide
  have hdescent : baseEnd_3507549 < baseStart_3507549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507553 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3507553 : Nat := 118140960795 + 3507553 * 2 ^ 59
def prefixEnd_3507553 : Nat := 4983230072969 + 3 ^ 40 * 3507553 * 2
def baseEnd_3507553 : Nat := 600353536706606805485521

theorem tailTrace_3507553 : CollatzResearch.WordTrace tailWord_3507553 prefixEnd_3507553 600353536706606805485521 := by
  unfold tailWord_3507553
  simp only [CollatzResearch.WordTrace]
  refine ⟨127930967861741998205311313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85287311907827998803540875 127930967861741998205311313)
  ·
    refine ⟨95948225896306498653983485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127930967861741998205311313 95948225896306498653983485)
    ·
      refine ⟨35980584711114936995243807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95948225896306498653983485 35980584711114936995243807)
      ·
        refine ⟨53970877066672405492865711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35980584711114936995243807 53970877066672405492865711)
        ·
          refine ⟨80956315600008608239298567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53970877066672405492865711 80956315600008608239298567)
          ·
            refine ⟨121434473400012912358947851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80956315600008608239298567 121434473400012912358947851)
            ·
              refine ⟨182151710100019368538421777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121434473400012912358947851 182151710100019368538421777)
              ·
                refine ⟨136613782575014526403816333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182151710100019368538421777 136613782575014526403816333)
                ·
                  refine ⟨51230168465630447401431125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136613782575014526403816333 51230168465630447401431125)
                  ·
                    refine ⟨600353536706606805485521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51230168465630447401431125 600353536706606805485521)
                    ·
                      rfl

theorem cell23_3507553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3507553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507553 prefixEnd_3507553 := by exact prefixLift 3507553
  have htrace : WordTrace (prefixWord ++ tailWord_3507553) baseStart_3507553 baseEnd_3507553 := by
    simpa [prefixWord, tailWord_3507553, baseEnd_3507553] using wordTrace_append hprefix tailTrace_3507553
  have hstable : (prefixWord ++ tailWord_3507553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507553).length < 2 ^ (prefixWord ++ tailWord_3507553).sum := by decide
  have hdescent : baseEnd_3507553 < baseStart_3507553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507570 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3507570 : Nat := 118140960795 + 3507570 * 2 ^ 59
def prefixEnd_3507570 : Nat := 4983230072969 + 3 ^ 40 * 3507570 * 2
def baseEnd_3507570 : Nat := 600356446430315616647995

theorem tailTrace_3507570 : CollatzResearch.WordTrace tailWord_3507570 prefixEnd_3507570 600356446430315616647995 := by
  unfold tailWord_3507570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31982896975670102527170041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85287725268453606739120109 31982896975670102527170041)
  ·
    refine ⟨23987172731752576895377531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31982896975670102527170041 23987172731752576895377531)
    ·
      refine ⟨35980759097628865343066297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23987172731752576895377531 35980759097628865343066297)
      ·
        refine ⟨26985569323221649007299723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35980759097628865343066297 26985569323221649007299723)
        ·
          refine ⟨40478353984832473510949585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26985569323221649007299723 40478353984832473510949585)
          ·
            refine ⟨30358765488624355133212189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40478353984832473510949585 30358765488624355133212189)
            ·
              refine ⟨11384537058234133174954571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30358765488624355133212189 11384537058234133174954571)
              ·
                refine ⟨17076805587351199762431857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11384537058234133174954571 17076805587351199762431857)
                ·
                  refine ⟨12807604190513399821823893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17076805587351199762431857 12807604190513399821823893)
                  ·
                    refine ⟨600356446430315616647995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12807604190513399821823893 600356446430315616647995)
                    ·
                      rfl

theorem cell23_3507570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3507570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507570 prefixEnd_3507570 := by exact prefixLift 3507570
  have htrace : WordTrace (prefixWord ++ tailWord_3507570) baseStart_3507570 baseEnd_3507570 := by
    simpa [prefixWord, tailWord_3507570, baseEnd_3507570] using wordTrace_append hprefix tailTrace_3507570
  have hstable : (prefixWord ++ tailWord_3507570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507570).length < 2 ^ (prefixWord ++ tailWord_3507570).sum := by decide
  have hdescent : baseEnd_3507570 < baseStart_3507570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507577 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 1, 4, 2]
def baseStart_3507577 : Nat := 118140960795 + 3507577 * 2 ^ 59
def prefixEnd_3507577 : Nat := 4983230072969 + 3 ^ 40 * 3507577 * 2
def baseEnd_3507577 : Nat := 1801072933655528322556453

theorem tailTrace_3507577 : CollatzResearch.WordTrace tailWord_3507577 prefixEnd_3507577 1801072933655528322556453 := by
  unfold tailWord_3507577
  simp only [CollatzResearch.WordTrace]
  refine ⟨127931843213655050304184985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85287895475770033536123323 127931843213655050304184985)
  ·
    refine ⟨95948882410241287728138739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127931843213655050304184985 95948882410241287728138739)
    ·
      refine ⟨143923323615361931592208109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95948882410241287728138739 143923323615361931592208109)
      ·
        refine ⟨53971246355760724347078041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143923323615361931592208109 53971246355760724347078041)
        ·
          refine ⟨40478434766820543260308531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53971246355760724347078041 40478434766820543260308531)
          ·
            refine ⟨60717652150230814890462797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40478434766820543260308531 60717652150230814890462797)
            ·
              refine ⟨22769119556336555583923549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60717652150230814890462797 22769119556336555583923549)
              ·
                refine ⟨8538419833626208343971331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22769119556336555583923549 8538419833626208343971331)
                ·
                  refine ⟨12807629750439312515956997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538419833626208343971331 12807629750439312515956997)
                  ·
                    refine ⟨2401430578207371096741937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12807629750439312515956997 2401430578207371096741937)
                    ·
                      refine ⟨1801072933655528322556453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401430578207371096741937 1801072933655528322556453)
                      ·
                        rfl

theorem cell23_3507577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_3507577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507577 prefixEnd_3507577 := by exact prefixLift 3507577
  have htrace : WordTrace (prefixWord ++ tailWord_3507577) baseStart_3507577 baseEnd_3507577 := by
    simpa [prefixWord, tailWord_3507577, baseEnd_3507577] using wordTrace_append hprefix tailTrace_3507577
  have hstable : (prefixWord ++ tailWord_3507577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507577).length < 2 ^ (prefixWord ++ tailWord_3507577).sum := by decide
  have hdescent : baseEnd_3507577 < baseStart_3507577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507580 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3507580 : Nat := 118140960795 + 3507580 * 2 ^ 59
def prefixEnd_3507580 : Nat := 4983230072969 + 3 ^ 40 * 3507580 * 2
def baseEnd_3507580 : Nat := 1801074474097491810818939

theorem tailTrace_3507580 : CollatzResearch.WordTrace tailWord_3507580 prefixEnd_3507580 1801074474097491810818939 := by
  unfold tailWord_3507580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63965976316322090908272097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85287968421762787877696129 63965976316322090908272097)
  ·
    refine ⟨47974482237241568181204073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63965976316322090908272097 47974482237241568181204073)
    ·
      refine ⟨35980861677931176135903055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47974482237241568181204073 35980861677931176135903055)
      ·
        refine ⟨53971292516896764203854583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35980861677931176135903055 53971292516896764203854583)
        ·
          refine ⟨80956938775345146305781875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53971292516896764203854583 80956938775345146305781875)
          ·
            refine ⟨121435408163017719458672813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80956938775345146305781875 121435408163017719458672813)
            ·
              refine ⟨45538278061131644797002305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121435408163017719458672813 45538278061131644797002305)
              ·
                refine ⟨34153708545848733597751729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45538278061131644797002305 34153708545848733597751729)
                ·
                  refine ⟨25615281409386550198313797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34153708545848733597751729 25615281409386550198313797)
                  ·
                    refine ⟨4802865264259978162183837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25615281409386550198313797 4802865264259978162183837)
                    ·
                      refine ⟨1801074474097491810818939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4802865264259978162183837 1801074474097491810818939)
                      ·
                        rfl

theorem cell23_3507580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3507580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507580 prefixEnd_3507580 := by exact prefixLift 3507580
  have htrace : WordTrace (prefixWord ++ tailWord_3507580) baseStart_3507580 baseEnd_3507580 := by
    simpa [prefixWord, tailWord_3507580, baseEnd_3507580] using wordTrace_append hprefix tailTrace_3507580
  have hstable : (prefixWord ++ tailWord_3507580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507580).length < 2 ^ (prefixWord ++ tailWord_3507580).sum := by decide
  have hdescent : baseEnd_3507580 < baseStart_3507580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507680 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_3507680 : Nat := 118140960795 + 3507680 * 2 ^ 59
def prefixEnd_3507680 : Nat := 4983230072969 + 3 ^ 40 * 3507680 * 2
def baseEnd_3507680 : Nat := 1801125822162941419568479

theorem tailTrace_3507680 : CollatzResearch.WordTrace tailWord_3507680 prefixEnd_3507680 1801125822162941419568479 := by
  unfold tailWord_3507680
  simp only [CollatzResearch.WordTrace]
  refine ⟨63967799966140949447592247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85290399954854599263456329 63967799966140949447592247)
  ·
    refine ⟨95951699949211424171388371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63967799966140949447592247 95951699949211424171388371)
    ·
      refine ⟨143927549923817136257082557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95951699949211424171388371 143927549923817136257082557)
      ·
        refine ⟨53972831221431426096405959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143927549923817136257082557 53972831221431426096405959)
        ·
          refine ⟨80959246832147139144608939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53972831221431426096405959 80959246832147139144608939)
          ·
            refine ⟨121438870248220708716913409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80959246832147139144608939 121438870248220708716913409)
            ·
              refine ⟨91079152686165531537685057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121438870248220708716913409 91079152686165531537685057)
              ·
                refine ⟨68309364514624148653263793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91079152686165531537685057 68309364514624148653263793)
                ·
                  refine ⟨51232023385968111489947845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68309364514624148653263793 51232023385968111489947845)
                  ·
                    refine ⟨9606004384869020904365221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51232023385968111489947845 9606004384869020904365221)
                    ·
                      refine ⟨1801125822162941419568479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9606004384869020904365221 1801125822162941419568479)
                      ·
                        rfl

theorem cell23_3507680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_3507680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507680 prefixEnd_3507680 := by exact prefixLift 3507680
  have htrace : WordTrace (prefixWord ++ tailWord_3507680) baseStart_3507680 baseEnd_3507680 := by
    simpa [prefixWord, tailWord_3507680, baseEnd_3507680] using wordTrace_append hprefix tailTrace_3507680
  have hstable : (prefixWord ++ tailWord_3507680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507680).length < 2 ^ (prefixWord ++ tailWord_3507680).sum := by decide
  have hdescent : baseEnd_3507680 < baseStart_3507680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507701 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3507701 : Nat := 118140960795 + 3507701 * 2 ^ 59
def prefixEnd_3507701 : Nat := 4983230072969 + 3 ^ 40 * 3507701 * 2
def baseEnd_3507701 : Nat := 1801136605256685837405883

theorem tailTrace_3507701 : CollatzResearch.WordTrace tailWord_3507701 prefixEnd_3507701 1801136605256685837405883 := by
  unfold tailWord_3507701
  simp only [CollatzResearch.WordTrace]
  refine ⟨127936365865205819481698957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85290910576803879654465971 127936365865205819481698957)
  ·
    refine ⟨47976137199452182305637109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127936365865205819481698957 47976137199452182305637109)
    ·
      refine ⟨4497762862448642091153479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47976137199452182305637109 4497762862448642091153479)
      ·
        refine ⟨6746644293672963136730219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497762862448642091153479 6746644293672963136730219)
        ·
          refine ⟨10119966440509444705095329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746644293672963136730219 10119966440509444705095329)
          ·
            refine ⟨7589974830382083528821497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119966440509444705095329 7589974830382083528821497)
            ·
              refine ⟨5692481122786562646616123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589974830382083528821497 5692481122786562646616123)
              ·
                refine ⟨8538721684179843969924185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692481122786562646616123 8538721684179843969924185)
                ·
                  refine ⟨6404041263134882977443139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538721684179843969924185 6404041263134882977443139)
                  ·
                    refine ⟨9606061894702324466164709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6404041263134882977443139 9606061894702324466164709)
                    ·
                      refine ⟨1801136605256685837405883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9606061894702324466164709 1801136605256685837405883)
                      ·
                        rfl

theorem cell23_3507701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3507701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507701 prefixEnd_3507701 := by exact prefixLift 3507701
  have htrace : WordTrace (prefixWord ++ tailWord_3507701) baseStart_3507701 baseEnd_3507701 := by
    simpa [prefixWord, tailWord_3507701, baseEnd_3507701] using wordTrace_append hprefix tailTrace_3507701
  have hstable : (prefixWord ++ tailWord_3507701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507701).length < 2 ^ (prefixWord ++ tailWord_3507701).sum := by decide
  have hdescent : baseEnd_3507701 < baseStart_3507701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507704 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_3507704 : Nat := 118140960795 + 3507704 * 2 ^ 59
def prefixEnd_3507704 : Nat := 4983230072969 + 3 ^ 40 * 3507704 * 2
def baseEnd_3507704 : Nat := 1801138145698649325668369

theorem tailTrace_3507704 : CollatzResearch.WordTrace tailWord_3507704 prefixEnd_3507704 1801138145698649325668369 := by
  unfold tailWord_3507704
  simp only [CollatzResearch.WordTrace]
  refine ⟨63968237642097475497029083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85290983522796633996038777 63968237642097475497029083)
  ·
    refine ⟨95952356463146213245543625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63968237642097475497029083 95952356463146213245543625)
    ·
      refine ⟨71964267347359659934157719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95952356463146213245543625 71964267347359659934157719)
      ·
        refine ⟨107946401021039489901236579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71964267347359659934157719 107946401021039489901236579)
        ·
          refine ⟨161919601531559234851854869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107946401021039489901236579 161919601531559234851854869)
          ·
            refine ⟨7589981321791839133680697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161919601531559234851854869 7589981321791839133680697)
            ·
              refine ⟨5692485991343879350260523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589981321791839133680697 5692485991343879350260523)
              ·
                refine ⟨8538728987015819025390785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692485991343879350260523 8538728987015819025390785)
                ·
                  refine ⟨6404046740261864269043089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8538728987015819025390785 6404046740261864269043089)
                  ·
                    refine ⟨4803035055196398201782317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404046740261864269043089 4803035055196398201782317)
                    ·
                      refine ⟨1801138145698649325668369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803035055196398201782317 1801138145698649325668369)
                      ·
                        rfl

theorem cell23_3507704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_3507704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507704 prefixEnd_3507704 := by exact prefixLift 3507704
  have htrace : WordTrace (prefixWord ++ tailWord_3507704) baseStart_3507704 baseEnd_3507704 := by
    simpa [prefixWord, tailWord_3507704, baseEnd_3507704] using wordTrace_append hprefix tailTrace_3507704
  have hstable : (prefixWord ++ tailWord_3507704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507704).length < 2 ^ (prefixWord ++ tailWord_3507704).sum := by decide
  have hdescent : baseEnd_3507704 < baseStart_3507704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507724 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 6]
def baseStart_3507724 : Nat := 118140960795 + 3507724 * 2 ^ 59
def prefixEnd_3507724 : Nat := 4983230072969 + 3 ^ 40 * 3507724 * 2
def baseEnd_3507724 : Nat := 200127601701304360824253

theorem tailTrace_3507724 : CollatzResearch.WordTrace tailWord_3507724 prefixEnd_3507724 200127601701304360824253 := by
  unfold tailWord_3507724
  simp only [CollatzResearch.WordTrace]
  refine ⟨63968602372061247204893113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85291469829414996273190817 63968602372061247204893113)
  ·
    refine ⟨47976451779045935403669835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63968602372061247204893113 47976451779045935403669835)
    ·
      refine ⟨71964677668568903105504753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47976451779045935403669835 71964677668568903105504753)
      ·
        refine ⟨53973508251426677329128565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71964677668568903105504753 53973508251426677329128565)
        ·
          refine ⟨5060016398571250999605803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53973508251426677329128565 5060016398571250999605803)
          ·
            refine ⟨7590024597856876499408705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060016398571250999605803 7590024597856876499408705)
            ·
              refine ⟨5692518448392657374556529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590024597856876499408705 5692518448392657374556529)
              ·
                refine ⟨4269388836294493030917397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692518448392657374556529 4269388836294493030917397)
                ·
                  refine ⟨200127601701304360824253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4269388836294493030917397 200127601701304360824253)
                  ·
                    rfl

theorem cell23_3507724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_3507724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507724 prefixEnd_3507724 := by exact prefixLift 3507724
  have htrace : WordTrace (prefixWord ++ tailWord_3507724) baseStart_3507724 baseEnd_3507724 := by
    simpa [prefixWord, tailWord_3507724, baseEnd_3507724] using wordTrace_append hprefix tailTrace_3507724
  have hstable : (prefixWord ++ tailWord_3507724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507724).length < 2 ^ (prefixWord ++ tailWord_3507724).sum := by decide
  have hdescent : baseEnd_3507724 < baseStart_3507724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507754 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3507754 : Nat := 118140960795 + 3507754 * 2 ^ 59
def prefixEnd_3507754 : Nat := 4983230072969 + 3 ^ 40 * 3507754 * 2
def baseEnd_3507754 : Nat := 600387939910458043347713

theorem tailTrace_3507754 : CollatzResearch.WordTrace tailWord_3507754 prefixEnd_3507754 600387939910458043347713 := by
  unfold tailWord_3507754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31984574733503452383344579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85292199289342539688918877 31984574733503452383344579)
  ·
    refine ⟨47976862100255178575016869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31984574733503452383344579 47976862100255178575016869)
    ·
      refine ⟨8995661643797845982815663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47976862100255178575016869 8995661643797845982815663)
      ·
        refine ⟨13493492465696768974223495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995661643797845982815663 13493492465696768974223495)
        ·
          refine ⟨20240238698545153461335243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493492465696768974223495 20240238698545153461335243)
          ·
            refine ⟨30360358047817730192002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240238698545153461335243 30360358047817730192002865)
            ·
              refine ⟨22770268535863297644002149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30360358047817730192002865 22770268535863297644002149)
              ·
                refine ⟨4269425350474368308250403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22770268535863297644002149 4269425350474368308250403)
                ·
                  refine ⟨6404138025711552462375605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269425350474368308250403 6404138025711552462375605)
                  ·
                    refine ⟨600387939910458043347713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6404138025711552462375605 600387939910458043347713)
                    ·
                      rfl

theorem cell23_3507754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3507754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507754 prefixEnd_3507754 := by exact prefixLift 3507754
  have htrace : WordTrace (prefixWord ++ tailWord_3507754) baseStart_3507754 baseEnd_3507754 := by
    simpa [prefixWord, tailWord_3507754, baseEnd_3507754] using wordTrace_append hprefix tailTrace_3507754
  have hstable : (prefixWord ++ tailWord_3507754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507754).length < 2 ^ (prefixWord ++ tailWord_3507754).sum := by decide
  have hdescent : baseEnd_3507754 < baseStart_3507754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507767 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 1, 6]
def baseStart_3507767 : Nat := 118140960795 + 3507767 * 2 ^ 59
def prefixEnd_3507767 : Nat := 4983230072969 + 3 ^ 40 * 3507767 * 2
def baseEnd_3507767 : Nat := 600390164993294193060193

theorem tailTrace_3507767 : CollatzResearch.WordTrace tailWord_3507767 prefixEnd_3507767 600390164993294193060193 := by
  unfold tailWord_3507767
  simp only [CollatzResearch.WordTrace]
  refine ⟨127938773082966712753601555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85292515388644475169067703 127938773082966712753601555)
  ·
    refine ⟨191908159624450069130402333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127938773082966712753601555 191908159624450069130402333)
    ·
      refine ⟨71965559859168775923900875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191908159624450069130402333 71965559859168775923900875)
      ·
        refine ⟨107948339788753163885851313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71965559859168775923900875 107948339788753163885851313)
        ·
          refine ⟨80961254841564872914388485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107948339788753163885851313 80961254841564872914388485)
          ·
            refine ⟨15180235282793413671447841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80961254841564872914388485 15180235282793413671447841)
            ·
              refine ⟨11385176462095060253585881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15180235282793413671447841 11385176462095060253585881)
              ·
                refine ⟨8538882346571295190189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385176462095060253585881 8538882346571295190189411)
                ·
                  refine ⟨12808323519856942785284117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538882346571295190189411 12808323519856942785284117)
                  ·
                    refine ⟨600390164993294193060193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12808323519856942785284117 600390164993294193060193)
                    ·
                      rfl

theorem cell23_3507767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_3507767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507767 prefixEnd_3507767 := by exact prefixLift 3507767
  have htrace : WordTrace (prefixWord ++ tailWord_3507767) baseStart_3507767 baseEnd_3507767 := by
    simpa [prefixWord, tailWord_3507767, baseEnd_3507767] using wordTrace_append hprefix tailTrace_3507767
  have hstable : (prefixWord ++ tailWord_3507767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507767).length < 2 ^ (prefixWord ++ tailWord_3507767).sum := by decide
  have hdescent : baseEnd_3507767 < baseStart_3507767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507768 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 1, 1, 3]
def baseStart_3507768 : Nat := 118140960795 + 3507768 * 2 ^ 59
def prefixEnd_3507768 : Nat := 4983230072969 + 3 ^ 40 * 3507768 * 2
def baseEnd_3507768 : Nat := 1801171008460537075268075

theorem tailTrace_3507768 : CollatzResearch.WordTrace tailWord_3507768 prefixEnd_3507768 1801171008460537075268075 := by
  unfold tailWord_3507768
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969404777981544962193979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85292539703975393282925305 63969404777981544962193979)
  ·
    refine ⟨95954107166972317443290969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63969404777981544962193979 95954107166972317443290969)
    ·
      refine ⟨71965580375229238082468227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95954107166972317443290969 71965580375229238082468227)
      ·
        refine ⟨107948370562843857123702341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71965580375229238082468227 107948370562843857123702341)
        ·
          refine ⟨20240319480533223210694189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107948370562843857123702341 20240319480533223210694189)
          ·
            refine ⟨7590119805199958704010321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20240319480533223210694189 7590119805199958704010321)
            ·
              refine ⟨5692589853899969028007741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590119805199958704010321 5692589853899969028007741)
              ·
                refine ⟨2134721195212488385502903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5692589853899969028007741 2134721195212488385502903)
                ·
                  refine ⟨3202081792818732578254355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134721195212488385502903 3202081792818732578254355)
                  ·
                    refine ⟨4803122689228098867381533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3202081792818732578254355 4803122689228098867381533)
                    ·
                      refine ⟨1801171008460537075268075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803122689228098867381533 1801171008460537075268075)
                      ·
                        rfl

theorem cell23_3507768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_3507768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507768 prefixEnd_3507768 := by exact prefixLift 3507768
  have htrace : WordTrace (prefixWord ++ tailWord_3507768) baseStart_3507768 baseEnd_3507768 := by
    simpa [prefixWord, tailWord_3507768, baseEnd_3507768] using wordTrace_append hprefix tailTrace_3507768
  have hstable : (prefixWord ++ tailWord_3507768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507768).length < 2 ^ (prefixWord ++ tailWord_3507768).sum := by decide
  have hdescent : baseEnd_3507768 < baseStart_3507768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507794 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3507794 : Nat := 118140960795 + 3507794 * 2 ^ 59
def prefixEnd_3507794 : Nat := 4983230072969 + 3 ^ 40 * 3507794 * 2
def baseEnd_3507794 : Nat := 1801184358957553973542955

theorem tailTrace_3507794 : CollatzResearch.WordTrace tailWord_3507794 prefixEnd_3507794 1801184358957553973542955 := by
  unfold tailWord_3507794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31984939463467224091208609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85293171902579264243222957 31984939463467224091208609)
  ·
    refine ⟨23988704597600418068406457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31984939463467224091208609 23988704597600418068406457)
    ·
      refine ⟨17991528448200313551304843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23988704597600418068406457 17991528448200313551304843)
      ·
        refine ⟨26987292672300470326957265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991528448200313551304843 26987292672300470326957265)
        ·
          refine ⟨20240469504225352745217949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26987292672300470326957265 20240469504225352745217949)
          ·
            refine ⟨7590176064084507279456731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20240469504225352745217949 7590176064084507279456731)
            ·
              refine ⟨11385264096126760919185097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590176064084507279456731 11385264096126760919185097)
              ·
                refine ⟨8538948072095070689388823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385264096126760919185097 8538948072095070689388823)
                ·
                  refine ⟨12808422108142606034083235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8538948072095070689388823 12808422108142606034083235)
                  ·
                    refine ⟨19212633162213909051124853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12808422108142606034083235 19212633162213909051124853)
                    ·
                      refine ⟨1801184358957553973542955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19212633162213909051124853 1801184358957553973542955)
                      ·
                        rfl

theorem cell23_3507794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3507794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507794 prefixEnd_3507794 := by exact prefixLift 3507794
  have htrace : WordTrace (prefixWord ++ tailWord_3507794) baseStart_3507794 baseEnd_3507794 := by
    simpa [prefixWord, tailWord_3507794, baseEnd_3507794] using wordTrace_append hprefix tailTrace_3507794
  have hstable : (prefixWord ++ tailWord_3507794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507794).length < 2 ^ (prefixWord ++ tailWord_3507794).sum := by decide
  have hdescent : baseEnd_3507794 < baseStart_3507794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507804 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3507804 : Nat := 118140960795 + 3507804 * 2 ^ 59
def prefixEnd_3507804 : Nat := 4983230072969 + 3 ^ 40 * 3507804 * 2
def baseEnd_3507804 : Nat := 1801189493764098934417909

theorem tailTrace_3507804 : CollatzResearch.WordTrace tailWord_3507804 prefixEnd_3507804 1801189493764098934417909 := by
  unfold tailWord_3507804
  simp only [CollatzResearch.WordTrace]
  refine ⟨63970061291916334036349233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85293415055888445381798977 63970061291916334036349233)
  ·
    refine ⟨47977545968937250527261925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63970061291916334036349233 47977545968937250527261925)
    ·
      refine ⟨8995789869175734473861611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47977545968937250527261925 8995789869175734473861611)
      ·
        refine ⟨13493684803763601710792417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995789869175734473861611 13493684803763601710792417)
        ·
          refine ⟨10120263602822701283094313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13493684803763601710792417 10120263602822701283094313)
          ·
            refine ⟨7590197702117025962320735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120263602822701283094313 7590197702117025962320735)
            ·
              refine ⟨11385296553175538943481103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590197702117025962320735 11385296553175538943481103)
              ·
                refine ⟨17077944829763308415221655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385296553175538943481103 17077944829763308415221655)
                ·
                  refine ⟨25616917244644962622832483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17077944829763308415221655 25616917244644962622832483)
                  ·
                    refine ⟨38425375866967443934248725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25616917244644962622832483 38425375866967443934248725)
                    ·
                      refine ⟨1801189493764098934417909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38425375866967443934248725 1801189493764098934417909)
                      ·
                        rfl

theorem cell23_3507804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3507804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507804 prefixEnd_3507804 := by exact prefixLift 3507804
  have htrace : WordTrace (prefixWord ++ tailWord_3507804) baseStart_3507804 baseEnd_3507804 := by
    simpa [prefixWord, tailWord_3507804, baseEnd_3507804] using wordTrace_append hprefix tailTrace_3507804
  have hstable : (prefixWord ++ tailWord_3507804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507804).length < 2 ^ (prefixWord ++ tailWord_3507804).sum := by decide
  have hdescent : baseEnd_3507804 < baseStart_3507804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507811 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 3]
def baseStart_3507811 : Nat := 118140960795 + 3507811 * 2 ^ 59
def prefixEnd_3507811 : Nat := 4983230072969 + 3 ^ 40 * 3507811 * 2
def baseEnd_3507811 : Nat := 1801193088128680407030377

theorem tailTrace_3507811 : CollatzResearch.WordTrace tailWord_3507811 prefixEnd_3507811 1801193088128680407030377 := by
  unfold tailWord_3507811
  simp only [CollatzResearch.WordTrace]
  refine ⟨127940377894807308268203287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85293585263204872178802191 127940377894807308268203287)
  ·
    refine ⟨191910566842210962402304931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127940377894807308268203287 191910566842210962402304931)
    ·
      refine ⟨287865850263316443603457397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191910566842210962402304931 287865850263316443603457397)
      ·
        refine ⟨26987423462185916587824131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287865850263316443603457397 26987423462185916587824131)
        ·
          refine ⟨40481135193278874881736197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26987423462185916587824131 40481135193278874881736197)
          ·
            refine ⟨7590212848739789040325537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40481135193278874881736197 7590212848739789040325537)
            ·
              refine ⟨5692659636554841780244153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590212848739789040325537 5692659636554841780244153)
              ·
                refine ⟨4269494727416131335183115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692659636554841780244153 4269494727416131335183115)
                ·
                  refine ⟨6404242091124197002774673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269494727416131335183115 6404242091124197002774673)
                  ·
                    refine ⟨4803181568343147752081005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404242091124197002774673 4803181568343147752081005)
                    ·
                      refine ⟨1801193088128680407030377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803181568343147752081005 1801193088128680407030377)
                      ·
                        rfl

theorem cell23_3507811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_3507811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507811 prefixEnd_3507811 := by exact prefixLift 3507811
  have htrace : WordTrace (prefixWord ++ tailWord_3507811) baseStart_3507811 baseEnd_3507811 := by
    simpa [prefixWord, tailWord_3507811, baseEnd_3507811] using wordTrace_append hprefix tailTrace_3507811
  have hstable : (prefixWord ++ tailWord_3507811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507811).length < 2 ^ (prefixWord ++ tailWord_3507811).sum := by decide
  have hdescent : baseEnd_3507811 < baseStart_3507811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507841 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3507841 : Nat := 118140960795 + 3507841 * 2 ^ 59
def prefixEnd_3507841 : Nat := 4983230072969 + 3 ^ 40 * 3507841 * 2
def baseEnd_3507841 : Nat := 1801208492548315289655239

theorem tailTrace_3507841 : CollatzResearch.WordTrace tailWord_3507841 prefixEnd_3507841 1801208492548315289655239 := by
  unfold tailWord_3507841
  simp only [CollatzResearch.WordTrace]
  refine ⟨127941472084698623391795377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85294314723132415594530251 127941472084698623391795377)
  ·
    refine ⟨95956104063523967543846533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127941472084698623391795377 95956104063523967543846533)
    ·
      refine ⟨17991769511910743914471225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95956104063523967543846533 17991769511910743914471225)
      ·
        refine ⟨13493827133933057935853419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991769511910743914471225 13493827133933057935853419)
        ·
          refine ⟨20240740700899586903780129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493827133933057935853419 20240740700899586903780129)
          ·
            refine ⟨15180555525674690177835097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20240740700899586903780129 15180555525674690177835097)
            ·
              refine ⟨11385416644256017633376323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15180555525674690177835097 11385416644256017633376323)
              ·
                refine ⟨17078124966384026450064485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385416644256017633376323 17078124966384026450064485)
                ·
                  refine ⟨3202148431197004959387091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17078124966384026450064485 3202148431197004959387091)
                  ·
                    refine ⟨4803222646795507439080637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3202148431197004959387091 4803222646795507439080637)
                    ·
                      refine ⟨1801208492548315289655239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803222646795507439080637 1801208492548315289655239)
                      ·
                        rfl

theorem cell23_3507841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3507841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507841 prefixEnd_3507841 := by exact prefixLift 3507841
  have htrace : WordTrace (prefixWord ++ tailWord_3507841) baseStart_3507841 baseEnd_3507841 := by
    simpa [prefixWord, tailWord_3507841, baseEnd_3507841] using wordTrace_append hprefix tailTrace_3507841
  have hstable : (prefixWord ++ tailWord_3507841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507841).length < 2 ^ (prefixWord ++ tailWord_3507841).sum := by decide
  have hdescent : baseEnd_3507841 < baseStart_3507841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507868 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3507868 : Nat := 118140960795 + 3507868 * 2 ^ 59
def prefixEnd_3507868 : Nat := 4983230072969 + 3 ^ 40 * 3507868 * 2
def baseEnd_3507868 : Nat := 1801222356525986684017615

theorem tailTrace_3507868 : CollatzResearch.WordTrace tailWord_3507868 prefixEnd_3507868 1801222356525986684017615 := by
  unfold tailWord_3507868
  simp only [CollatzResearch.WordTrace]
  refine ⟨63971228427800403501514129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85294971237067204668685505 63971228427800403501514129)
  ·
    refine ⟨47978421320850302626135597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63971228427800403501514129 47978421320850302626135597)
    ·
      refine ⟨17991907995318863484800849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47978421320850302626135597 17991907995318863484800849)
      ·
        refine ⟨13493930996489147613600637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991907995318863484800849 13493930996489147613600637)
        ·
          refine ⟨5060224123683430355100239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13493930996489147613600637 5060224123683430355100239)
          ·
            refine ⟨7590336185525145532650359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060224123683430355100239 7590336185525145532650359)
            ·
              refine ⟨11385504278287718298975539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590336185525145532650359 11385504278287718298975539)
              ·
                refine ⟨17078256417431577448463309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385504278287718298975539 17078256417431577448463309)
                ·
                  refine ⟨6404346156536841543173741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17078256417431577448463309 6404346156536841543173741)
                  ·
                    refine ⟨2401629808701315578690153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6404346156536841543173741 2401629808701315578690153)
                    ·
                      refine ⟨1801222356525986684017615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401629808701315578690153 1801222356525986684017615)
                      ·
                        rfl

theorem cell23_3507868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3507868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507868 prefixEnd_3507868 := by exact prefixLift 3507868
  have htrace : WordTrace (prefixWord ++ tailWord_3507868) baseStart_3507868 baseEnd_3507868 := by
    simpa [prefixWord, tailWord_3507868, baseEnd_3507868] using wordTrace_append hprefix tailTrace_3507868
  have hstable : (prefixWord ++ tailWord_3507868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507868).length < 2 ^ (prefixWord ++ tailWord_3507868).sum := by decide
  have hdescent : baseEnd_3507868 < baseStart_3507868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507885 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_3507885 : Nat := 118140960795 + 3507885 * 2 ^ 59
def prefixEnd_3507885 : Nat := 4983230072969 + 3 ^ 40 * 3507885 * 2
def baseEnd_3507885 : Nat := 1801231085697113117505037

theorem tailTrace_3507885 : CollatzResearch.WordTrace tailWord_3507885 prefixEnd_3507885 1801231085697113117505037 := by
  unfold tailWord_3507885
  simp only [CollatzResearch.WordTrace]
  refine ⟨127943076896539218906397109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85295384597692812604264739 127943076896539218906397109)
  ·
    refine ⟨11994663459050551772474729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127943076896539218906397109 11994663459050551772474729)
    ·
      refine ⟨8995997594287913829356047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11994663459050551772474729 8995997594287913829356047)
      ·
        refine ⟨13493996391431870744034071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995997594287913829356047 13493996391431870744034071)
        ·
          refine ⟨20240994587147806116051107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493996391431870744034071 20240994587147806116051107)
          ·
            refine ⟨30361491880721709174076661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20240994587147806116051107 30361491880721709174076661)
            ·
              refine ⟨2846389863817660235069687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30361491880721709174076661 2846389863817660235069687)
              ·
                refine ⟨4269584795726490352604531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846389863817660235069687 4269584795726490352604531)
                ·
                  refine ⟨6404377193589735528906797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269584795726490352604531 6404377193589735528906797)
                  ·
                    refine ⟨2401641447596150823340049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6404377193589735528906797 2401641447596150823340049)
                    ·
                      refine ⟨1801231085697113117505037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401641447596150823340049 1801231085697113117505037)
                      ·
                        rfl

theorem cell23_3507885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_3507885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507885 prefixEnd_3507885 := by exact prefixLift 3507885
  have htrace : WordTrace (prefixWord ++ tailWord_3507885) baseStart_3507885 baseEnd_3507885 := by
    simpa [prefixWord, tailWord_3507885, baseEnd_3507885] using wordTrace_append hprefix tailTrace_3507885
  have hstable : (prefixWord ++ tailWord_3507885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507885).length < 2 ^ (prefixWord ++ tailWord_3507885).sum := by decide
  have hdescent : baseEnd_3507885 < baseStart_3507885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507897 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3507897 : Nat := 118140960795 + 3507897 * 2 ^ 59
def prefixEnd_3507897 : Nat := 4983230072969 + 3 ^ 40 * 3507897 * 2
def baseEnd_3507897 : Nat := 1801237247464967070554981

theorem tailTrace_3507897 : CollatzResearch.WordTrace tailWord_3507897 prefixEnd_3507897 1801237247464967070554981 := by
  unfold tailWord_3507897
  simp only [CollatzResearch.WordTrace]
  refine ⟨127943514572495744955833945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85295676381663829970555963 127943514572495744955833945)
  ·
    refine ⟨95957635929371808716875459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127943514572495744955833945 95957635929371808716875459)
    ·
      refine ⟨143936453894057713075313189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95957635929371808716875459 143936453894057713075313189)
      ·
        refine ⟨26988085105135821201621223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143936453894057713075313189 26988085105135821201621223)
        ·
          refine ⟨40482127657703731802431835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26988085105135821201621223 40482127657703731802431835)
          ·
            refine ⟨60723191486555597703647753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40482127657703731802431835 60723191486555597703647753)
            ·
              refine ⟨45542393614916698277735815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60723191486555597703647753 45542393614916698277735815)
              ·
                refine ⟨68313590422375047416603723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45542393614916698277735815 68313590422375047416603723)
                ·
                  refine ⟨102470385633562571124905585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68313590422375047416603723 102470385633562571124905585)
                  ·
                    refine ⟨76852789225171928343679189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102470385633562571124905585 76852789225171928343679189)
                    ·
                      refine ⟨1801237247464967070554981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76852789225171928343679189 1801237247464967070554981)
                      ·
                        rfl

theorem cell23_3507897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3507897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507897 prefixEnd_3507897 := by exact prefixLift 3507897
  have htrace : WordTrace (prefixWord ++ tailWord_3507897) baseStart_3507897 baseEnd_3507897 := by
    simpa [prefixWord, tailWord_3507897, baseEnd_3507897] using wordTrace_append hprefix tailTrace_3507897
  have hstable : (prefixWord ++ tailWord_3507897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507897).length < 2 ^ (prefixWord ++ tailWord_3507897).sum := by decide
  have hdescent : baseEnd_3507897 < baseStart_3507897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507898 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_3507898 : Nat := 118140960795 + 3507898 * 2 ^ 59
def prefixEnd_3507898 : Nat := 4983230072969 + 3 ^ 40 * 3507898 * 2
def baseEnd_3507898 : Nat := 1801237760945621566642477

theorem tailTrace_3507898 : CollatzResearch.WordTrace tailWord_3507898 prefixEnd_3507898 1801237760945621566642477 := by
  unfold tailWord_3507898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31985887761373030531655087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85295700696994748084413565 31985887761373030531655087)
  ·
    refine ⟨47978831642059545797482631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31985887761373030531655087 47978831642059545797482631)
    ·
      refine ⟨71968247463089318696223947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47978831642059545797482631 71968247463089318696223947)
      ·
        refine ⟨107952371194633978044335921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71968247463089318696223947 107952371194633978044335921)
        ·
          refine ⟨80964278395975483533251941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107952371194633978044335921 80964278395975483533251941)
          ·
            refine ⟨15180802199245403162484739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80964278395975483533251941 15180802199245403162484739)
            ·
              refine ⟨22771203298868104743727109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15180802199245403162484739 22771203298868104743727109)
              ·
                refine ⟨4269600618537769639448833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22771203298868104743727109 4269600618537769639448833)
                ·
                  refine ⟨3202200463903327229586625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4269600618537769639448833 3202200463903327229586625)
                  ·
                    refine ⟨2401650347927495422189969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3202200463903327229586625 2401650347927495422189969)
                    ·
                      refine ⟨1801237760945621566642477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401650347927495422189969 1801237760945621566642477)
                      ·
                        rfl

theorem cell23_3507898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_3507898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507898 prefixEnd_3507898 := by exact prefixLift 3507898
  have htrace : WordTrace (prefixWord ++ tailWord_3507898) baseStart_3507898 baseEnd_3507898 := by
    simpa [prefixWord, tailWord_3507898, baseEnd_3507898] using wordTrace_append hprefix tailTrace_3507898
  have hstable : (prefixWord ++ tailWord_3507898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507898).length < 2 ^ (prefixWord ++ tailWord_3507898).sum := by decide
  have hdescent : baseEnd_3507898 < baseStart_3507898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507971 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 2, 4, 2]
def baseStart_3507971 : Nat := 118140960795 + 3507971 * 2 ^ 59
def prefixEnd_3507971 : Nat := 4983230072969 + 3 ^ 40 * 3507971 * 2
def baseEnd_3507971 : Nat := 1801275245033399781029641

theorem tailTrace_3507971 : CollatzResearch.WordTrace tailWord_3507971 prefixEnd_3507971 1801275245033399781029641 := by
  unfold tailWord_3507971
  simp only [CollatzResearch.WordTrace]
  refine ⟨127946213574227655594027767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85297475716151770396018511 127946213574227655594027767)
  ·
    refine ⟨191919320361341483391041651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127946213574227655594027767 191919320361341483391041651)
    ·
      refine ⟨287878980542012225086562477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191919320361341483391041651 287878980542012225086562477)
      ·
        refine ⟨107954617703254584407460929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287878980542012225086562477 107954617703254584407460929)
        ·
          refine ⟨80965963277440938305595697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107954617703254584407460929 80965963277440938305595697)
          ·
            refine ⟨60724472458080703729196773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80965963277440938305595697 60724472458080703729196773)
            ·
              refine ⟨11385838585890131949224395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60724472458080703729196773 11385838585890131949224395)
              ·
                refine ⟨17078757878835197923836593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385838585890131949224395 17078757878835197923836593)
                ·
                  refine ⟨12809068409126398442877445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17078757878835197923836593 12809068409126398442877445)
                  ·
                    refine ⟨2401700326711199708039521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12809068409126398442877445 2401700326711199708039521)
                    ·
                      refine ⟨1801275245033399781029641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401700326711199708039521 1801275245033399781029641)
                      ·
                        rfl

theorem cell23_3507971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_3507971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507971 prefixEnd_3507971 := by exact prefixLift 3507971
  have htrace : WordTrace (prefixWord ++ tailWord_3507971) baseStart_3507971 baseEnd_3507971 := by
    simpa [prefixWord, tailWord_3507971, baseEnd_3507971] using wordTrace_append hprefix tailTrace_3507971
  have hstable : (prefixWord ++ tailWord_3507971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507971).length < 2 ^ (prefixWord ++ tailWord_3507971).sum := by decide
  have hdescent : baseEnd_3507971 < baseStart_3507971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507991 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3507991 : Nat := 118140960795 + 3507991 * 2 ^ 59
def prefixEnd_3507991 : Nat := 4983230072969 + 3 ^ 40 * 3507991 * 2
def baseEnd_3507991 : Nat := 1801285514646489702779549

theorem tailTrace_3507991 : CollatzResearch.WordTrace tailWord_3507991 prefixEnd_3507991 1801285514646489702779549 := by
  unfold tailWord_3507991
  simp only [CollatzResearch.WordTrace]
  refine ⟨127946943034155199009755827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85297962022770132673170551 127946943034155199009755827)
  ·
    refine ⟨191920414551232798514633741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127946943034155199009755827 191920414551232798514633741)
    ·
      refine ⟨71970155456712299442987653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191920414551232798514633741 71970155456712299442987653)
      ·
        refine ⟨13494404148133556145560185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71970155456712299442987653 13494404148133556145560185)
        ·
          refine ⟨10120803111100167109170139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13494404148133556145560185 10120803111100167109170139)
          ·
            refine ⟨15181204666650250663755209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120803111100167109170139 15181204666650250663755209)
            ·
              refine ⟨11385903499987687997816407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15181204666650250663755209 11385903499987687997816407)
              ·
                refine ⟨17078855249981531996724611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385903499987687997816407 17078855249981531996724611)
                ·
                  refine ⟨25618282874972297995086917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17078855249981531996724611 25618282874972297995086917)
                  ·
                    refine ⟨4803428039057305874078797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25618282874972297995086917 4803428039057305874078797)
                    ·
                      refine ⟨1801285514646489702779549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803428039057305874078797 1801285514646489702779549)
                      ·
                        rfl

theorem cell23_3507991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3507991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507991 prefixEnd_3507991 := by exact prefixLift 3507991
  have htrace : WordTrace (prefixWord ++ tailWord_3507991) baseStart_3507991 baseEnd_3507991 := by
    simpa [prefixWord, tailWord_3507991, baseEnd_3507991] using wordTrace_append hprefix tailTrace_3507991
  have hstable : (prefixWord ++ tailWord_3507991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507991).length < 2 ^ (prefixWord ++ tailWord_3507991).sum := by decide
  have hdescent : baseEnd_3507991 < baseStart_3507991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3507994 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_3507994 : Nat := 118140960795 + 3507994 * 2 ^ 59
def prefixEnd_3507994 : Nat := 4983230072969 + 3 ^ 40 * 3507994 * 2
def baseEnd_3507994 : Nat := 200143006120939243449115

theorem tailTrace_3507994 : CollatzResearch.WordTrace tailWord_3507994 prefixEnd_3507994 200143006120939243449115 := by
  unfold tailWord_3507994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31986763113286082630528759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85298034968762887014743357 31986763113286082630528759)
  ·
    refine ⟨47980144669929123945793139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31986763113286082630528759 47980144669929123945793139)
    ·
      refine ⟨71970217004893685918689709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47980144669929123945793139 71970217004893685918689709)
      ·
        refine ⟨26988831376835132219508641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71970217004893685918689709 26988831376835132219508641)
        ·
          refine ⟨20241623532626349164631481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26988831376835132219508641 20241623532626349164631481)
          ·
            refine ⟨15181217649469761873473611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20241623532626349164631481 15181217649469761873473611)
            ·
              refine ⟨22771826474204642810210417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181217649469761873473611 22771826474204642810210417)
              ·
                refine ⟨17078869855653482107657813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22771826474204642810210417 17078869855653482107657813)
                ·
                  refine ⟨200143006120939243449115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17078869855653482107657813 200143006120939243449115)
                  ·
                    rfl

theorem cell23_3507994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_3507994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3507994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3507994 prefixEnd_3507994 := by exact prefixLift 3507994
  have htrace : WordTrace (prefixWord ++ tailWord_3507994) baseStart_3507994 baseEnd_3507994 := by
    simpa [prefixWord, tailWord_3507994, baseEnd_3507994] using wordTrace_append hprefix tailTrace_3507994
  have hstable : (prefixWord ++ tailWord_3507994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3507994).length < 2 ^ (prefixWord ++ tailWord_3507994).sum := by decide
  have hdescent : baseEnd_3507994 < baseStart_3507994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3507994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508008 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3508008 : Nat := 118140960795 + 3508008 * 2 ^ 59
def prefixEnd_3508008 : Nat := 4983230072969 + 3 ^ 40 * 3508008 * 2
def baseEnd_3508008 : Nat := 1801294243817616136266971

theorem tailTrace_3508008 : CollatzResearch.WordTrace tailWord_3508008 prefixEnd_3508008 1801294243817616136266971 := by
  unfold tailWord_3508008
  simp only [CollatzResearch.WordTrace]
  refine ⟨63973781537546805456562339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85298375383395740608749785 63973781537546805456562339)
  ·
    refine ⟨95960672306320208184843509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63973781537546805456562339 95960672306320208184843509)
    ·
      refine ⟨8996313028717519517329079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95960672306320208184843509 8996313028717519517329079)
      ·
        refine ⟨13494469543076279275993619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996313028717519517329079 13494469543076279275993619)
        ·
          refine ⟨20241704314614418913990429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13494469543076279275993619 20241704314614418913990429)
          ·
            refine ⟨7590639117980407092746411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20241704314614418913990429 7590639117980407092746411)
            ·
              refine ⟨11385958676970610639119617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590639117980407092746411 11385958676970610639119617)
              ·
                refine ⟨8539469007727957979339713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11385958676970610639119617 8539469007727957979339713)
                ·
                  refine ⟨6404601755795968484504785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8539469007727957979339713 6404601755795968484504785)
                  ·
                    refine ⟨4803451316846976363378589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404601755795968484504785 4803451316846976363378589)
                    ·
                      refine ⟨1801294243817616136266971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803451316846976363378589 1801294243817616136266971)
                      ·
                        rfl

theorem cell23_3508008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3508008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508008 prefixEnd_3508008 := by exact prefixLift 3508008
  have htrace : WordTrace (prefixWord ++ tailWord_3508008) baseStart_3508008 baseEnd_3508008 := by
    simpa [prefixWord, tailWord_3508008, baseEnd_3508008] using wordTrace_append hprefix tailTrace_3508008
  have hstable : (prefixWord ++ tailWord_3508008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508008).length < 2 ^ (prefixWord ++ tailWord_3508008).sum := by decide
  have hdescent : baseEnd_3508008 < baseStart_3508008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508058 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_3508058 : Nat := 118140960795 + 3508058 * 2 ^ 59
def prefixEnd_3508058 : Nat := 4983230072969 + 3 ^ 40 * 3508058 * 2
def baseEnd_3508058 : Nat := 600439972616780313547247

theorem tailTrace_3508058 : CollatzResearch.WordTrace tailWord_3508058 prefixEnd_3508058 600439972616780313547247 := by
  unfold tailWord_3508058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31987346681228117363111207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85299591149941646301629885 31987346681228117363111207)
  ·
    refine ⟨47981020021842176044666811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31987346681228117363111207 47981020021842176044666811)
    ·
      refine ⟨71971530032763264067000217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47981020021842176044666811 71971530032763264067000217)
      ·
        refine ⟨53978647524572448050250163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71971530032763264067000217 53978647524572448050250163)
        ·
          refine ⟨80967971286858672075375245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53978647524572448050250163 80967971286858672075375245)
          ·
            refine ⟨30362989232572002028265717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80967971286858672075375245 30362989232572002028265717)
            ·
              refine ⟨2846530240553625190149911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30362989232572002028265717 2846530240553625190149911)
              ·
                refine ⟨4269795360830437785224867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846530240553625190149911 4269795360830437785224867)
                ·
                  refine ⟨6404693041245656677837301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269795360830437785224867 6404693041245656677837301)
                  ·
                    refine ⟨600439972616780313547247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6404693041245656677837301 600439972616780313547247)
                    ·
                      rfl

theorem cell23_3508058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_3508058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508058 prefixEnd_3508058 := by exact prefixLift 3508058
  have htrace : WordTrace (prefixWord ++ tailWord_3508058) baseStart_3508058 baseEnd_3508058 := by
    simpa [prefixWord, tailWord_3508058, baseEnd_3508058] using wordTrace_append hprefix tailTrace_3508058
  have hstable : (prefixWord ++ tailWord_3508058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508058).length < 2 ^ (prefixWord ++ tailWord_3508058).sum := by decide
  have hdescent : baseEnd_3508058 < baseStart_3508058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508078 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3508078 : Nat := 118140960795 + 3508078 * 2 ^ 59
def prefixEnd_3508078 : Nat := 4983230072969 + 3 ^ 40 * 3508078 * 2
def baseEnd_3508078 : Nat := 1801330187463430862391649

theorem tailTrace_3508078 : CollatzResearch.WordTrace tailWord_3508078 prefixEnd_3508078 1801330187463430862391649 := by
  unfold tailWord_3508078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993764523105001608521611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85300077456560008578781925 15993764523105001608521611)
  ·
    refine ⟨23990646784657502412782417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15993764523105001608521611 23990646784657502412782417)
    ·
      refine ⟨17992985088493126809586813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23990646784657502412782417 17992985088493126809586813)
      ·
        refine ⟨6747369408184922553595055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17992985088493126809586813 6747369408184922553595055)
        ·
          refine ⟨10121054112277383830392583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747369408184922553595055 10121054112277383830392583)
          ·
            refine ⟨15181581168416075745588875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10121054112277383830392583 15181581168416075745588875)
            ·
              refine ⟨22772371752624113618383313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181581168416075745588875 22772371752624113618383313)
              ·
                refine ⟨17079278814468085213787485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22772371752624113618383313 17079278814468085213787485)
                ·
                  refine ⟨6404729555425531955170307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17079278814468085213787485 6404729555425531955170307)
                  ·
                    refine ⟨9607094333138297932755461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6404729555425531955170307 9607094333138297932755461)
                    ·
                      refine ⟨1801330187463430862391649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9607094333138297932755461 1801330187463430862391649)
                      ·
                        rfl

theorem cell23_3508078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3508078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508078 prefixEnd_3508078 := by exact prefixLift 3508078
  have htrace : WordTrace (prefixWord ++ tailWord_3508078) baseStart_3508078 baseEnd_3508078 := by
    simpa [prefixWord, tailWord_3508078, baseEnd_3508078] using wordTrace_append hprefix tailTrace_3508078
  have hstable : (prefixWord ++ tailWord_3508078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508078).length < 2 ^ (prefixWord ++ tailWord_3508078).sum := by decide
  have hdescent : baseEnd_3508078 < baseStart_3508078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508081 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_3508081 : Nat := 118140960795 + 3508081 * 2 ^ 59
def prefixEnd_3508081 : Nat := 4983230072969 + 3 ^ 40 * 3508081 * 2
def baseEnd_3508081 : Nat := 1801331727905394350654135

theorem tailTrace_3508081 : CollatzResearch.WordTrace tailWord_3508081 prefixEnd_3508081 1801331727905394350654135 := by
  unfold tailWord_3508081
  simp only [CollatzResearch.WordTrace]
  refine ⟨127950225603829144380532097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85300150402552762920354731 127950225603829144380532097)
  ·
    refine ⟨95962669202871858285399073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127950225603829144380532097 95962669202871858285399073)
    ·
      refine ⟨71972001902153893714049305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95962669202871858285399073 71972001902153893714049305)
      ·
        refine ⟨53979001426615420285536979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71972001902153893714049305 53979001426615420285536979)
        ·
          refine ⟨80968502139923130428305469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53979001426615420285536979 80968502139923130428305469)
          ·
            refine ⟨30363188302471173910614551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80968502139923130428305469 30363188302471173910614551)
            ·
              refine ⟨45544782453706760865921827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30363188302471173910614551 45544782453706760865921827)
              ·
                refine ⟨68317173680560141298882741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45544782453706760865921827 68317173680560141298882741)
                ·
                  refine ⟨6404735032552513246770257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68317173680560141298882741 6404735032552513246770257)
                  ·
                    refine ⟨4803551274414384935077693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6404735032552513246770257 4803551274414384935077693)
                    ·
                      refine ⟨1801331727905394350654135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803551274414384935077693 1801331727905394350654135)
                      ·
                        rfl

theorem cell23_3508081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_3508081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508081 prefixEnd_3508081 := by exact prefixLift 3508081
  have htrace : WordTrace (prefixWord ++ tailWord_3508081) baseStart_3508081 baseEnd_3508081 := by
    simpa [prefixWord, tailWord_3508081, baseEnd_3508081] using wordTrace_append hprefix tailTrace_3508081
  have hstable : (prefixWord ++ tailWord_3508081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508081).length < 2 ^ (prefixWord ++ tailWord_3508081).sum := by decide
  have hdescent : baseEnd_3508081 < baseStart_3508081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508101 : List Nat := [1, 3, 1, 1, 3, 2, 5, 7]
def baseStart_3508101 : Nat := 118140960795 + 3508101 * 2 ^ 59
def prefixEnd_3508101 : Nat := 4983230072969 + 3 ^ 40 * 3508101 * 2
def baseEnd_3508101 : Nat := 66716370278462380459409

theorem tailTrace_3508101 : CollatzResearch.WordTrace tailWord_3508101 prefixEnd_3508101 66716370278462380459409 := by
  unfold tailWord_3508101
  simp only [CollatzResearch.WordTrace]
  refine ⟨127950955063756687796260157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85300636709171125197506771 127950955063756687796260157)
  ·
    refine ⟨47981608148908757923597559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127950955063756687796260157 47981608148908757923597559)
    ·
      refine ⟨71972412223363136885396339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47981608148908757923597559 71972412223363136885396339)
      ·
        refine ⟨107958618335044705328094509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71972412223363136885396339 107958618335044705328094509)
        ·
          refine ⟨40484481875641764498035441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107958618335044705328094509 40484481875641764498035441)
          ·
            refine ⟨30363361406731323373526581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40484481875641764498035441 30363361406731323373526581)
            ·
              refine ⟨2846565131881061566268117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30363361406731323373526581 2846565131881061566268117)
              ·
                refine ⟨66716370278462380459409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2846565131881061566268117 66716370278462380459409)
                ·
                  rfl

theorem cell23_3508101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 7].length) (baseStart_3508101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508101 prefixEnd_3508101 := by exact prefixLift 3508101
  have htrace : WordTrace (prefixWord ++ tailWord_3508101) baseStart_3508101 baseEnd_3508101 := by
    simpa [prefixWord, tailWord_3508101, baseEnd_3508101] using wordTrace_append hprefix tailTrace_3508101
  have hstable : (prefixWord ++ tailWord_3508101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508101).length < 2 ^ (prefixWord ++ tailWord_3508101).sum := by decide
  have hdescent : baseEnd_3508101 < baseStart_3508101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508142 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3508142 : Nat := 118140960795 + 3508142 * 2 ^ 59
def prefixEnd_3508142 : Nat := 4983230072969 + 3 ^ 40 * 3508142 * 2
def baseEnd_3508142 : Nat := 1801363050225318611991355

theorem tailTrace_3508142 : CollatzResearch.WordTrace tailWord_3508142 prefixEnd_3508142 1801363050225318611991355 := by
  unfold tailWord_3508142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994056307076018974812835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85301633637738767865668453 15994056307076018974812835)
  ·
    refine ⟨23991084460614028462219253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15994056307076018974812835 23991084460614028462219253)
    ·
      refine ⟨2249164168182565168333055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23991084460614028462219253 2249164168182565168333055)
      ·
        refine ⟨3373746252273847752499583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249164168182565168333055 3373746252273847752499583)
        ·
          refine ⟨5060619378410771628749375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373746252273847752499583 5060619378410771628749375)
          ·
            refine ⟨7590929067616157443124063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060619378410771628749375 7590929067616157443124063)
            ·
              refine ⟨11386393601424236164686095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590929067616157443124063 11386393601424236164686095)
              ·
                refine ⟨17079590402136354247029143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11386393601424236164686095 17079590402136354247029143)
                ·
                  refine ⟨25619385603204531370543715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17079590402136354247029143 25619385603204531370543715)
                  ·
                    refine ⟨38429078404806797055815573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25619385603204531370543715 38429078404806797055815573)
                    ·
                      refine ⟨1801363050225318611991355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38429078404806797055815573 1801363050225318611991355)
                      ·
                        rfl

theorem cell23_3508142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3508142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508142 prefixEnd_3508142 := by exact prefixLift 3508142
  have htrace : WordTrace (prefixWord ++ tailWord_3508142) baseStart_3508142 baseEnd_3508142 := by
    simpa [prefixWord, tailWord_3508142, baseEnd_3508142] using wordTrace_append hprefix tailTrace_3508142
  have hstable : (prefixWord ++ tailWord_3508142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508142).length < 2 ^ (prefixWord ++ tailWord_3508142).sum := by decide
  have hdescent : baseEnd_3508142 < baseStart_3508142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508145 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3508145 : Nat := 118140960795 + 3508145 * 2 ^ 59
def prefixEnd_3508145 : Nat := 4983230072969 + 3 ^ 40 * 3508145 * 2
def baseEnd_3508145 : Nat := 1801364590667282100253841

theorem tailTrace_3508145 : CollatzResearch.WordTrace tailWord_3508145 prefixEnd_3508145 1801364590667282100253841 := by
  unfold tailWord_3508145
  simp only [CollatzResearch.WordTrace]
  refine ⟨127952559875597283310861889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85301706583731522207241259 127952559875597283310861889)
  ·
    refine ⟨95964419906697962483146417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127952559875597283310861889 95964419906697962483146417)
    ·
      refine ⟨71973314930023471862359813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95964419906697962483146417 71973314930023471862359813)
      ·
        refine ⟨13494996549379400974192465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71973314930023471862359813 13494996549379400974192465)
        ·
          refine ⟨10121247412034550730644349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13494996549379400974192465 10121247412034550730644349)
          ·
            refine ⟨3795467779512956523991631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10121247412034550730644349 3795467779512956523991631)
            ·
              refine ⟨5693201669269434785987447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795467779512956523991631 5693201669269434785987447)
              ·
                refine ⟨8539802503904152178981171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693201669269434785987447 8539802503904152178981171)
                ·
                  refine ⟨12809703755856228268471757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8539802503904152178981171 12809703755856228268471757)
                  ·
                    refine ⟨4803638908446085600676909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12809703755856228268471757 4803638908446085600676909)
                    ·
                      refine ⟨1801364590667282100253841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4803638908446085600676909 1801364590667282100253841)
                      ·
                        rfl

theorem cell23_3508145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3508145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508145 prefixEnd_3508145 := by exact prefixLift 3508145
  have htrace : WordTrace (prefixWord ++ tailWord_3508145) baseStart_3508145 baseEnd_3508145 := by
    simpa [prefixWord, tailWord_3508145, baseEnd_3508145] using wordTrace_append hprefix tailTrace_3508145
  have hstable : (prefixWord ++ tailWord_3508145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508145).length < 2 ^ (prefixWord ++ tailWord_3508145).sum := by decide
  have hdescent : baseEnd_3508145 < baseStart_3508145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508171 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_3508171 : Nat := 118140960795 + 3508171 * 2 ^ 59
def prefixEnd_3508171 : Nat := 4983230072969 + 3 ^ 40 * 3508171 * 2
def baseEnd_3508171 : Nat := 1801377941164298998528721

theorem tailTrace_3508171 : CollatzResearch.WordTrace tailWord_3508171 prefixEnd_3508171 1801377941164298998528721 := by
  unfold tailWord_3508171
  simp only [CollatzResearch.WordTrace]
  refine ⟨127953508173503089751308367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85302338782335393167538911 127953508173503089751308367)
  ·
    refine ⟨191930262260254634626962551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127953508173503089751308367 191930262260254634626962551)
    ·
      refine ⟨287895393390381951940443827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191930262260254634626962551 287895393390381951940443827)
      ·
        refine ⟨431843090085572927910665741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287895393390381951940443827 431843090085572927910665741)
        ·
          refine ⟨161941158782089847966499653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431843090085572927910665741 161941158782089847966499653)
          ·
            refine ⟨30363967271641846493718685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161941158782089847966499653 30363967271641846493718685)
            ·
              refine ⟨11386487726865692435144507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30363967271641846493718685 11386487726865692435144507)
              ·
                refine ⟨17079731590298538652716761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11386487726865692435144507 17079731590298538652716761)
                ·
                  refine ⟨12809798692723903989537571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17079731590298538652716761 12809798692723903989537571)
                  ·
                    refine ⟨19214698039085855984306357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12809798692723903989537571 19214698039085855984306357)
                    ·
                      refine ⟨1801377941164298998528721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19214698039085855984306357 1801377941164298998528721)
                      ·
                        rfl

theorem cell23_3508171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_3508171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508171 prefixEnd_3508171 := by exact prefixLift 3508171
  have htrace : WordTrace (prefixWord ++ tailWord_3508171) baseStart_3508171 baseEnd_3508171 := by
    simpa [prefixWord, tailWord_3508171, baseEnd_3508171] using wordTrace_append hprefix tailTrace_3508171
  have hstable : (prefixWord ++ tailWord_3508171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508171).length < 2 ^ (prefixWord ++ tailWord_3508171).sum := by decide
  have hdescent : baseEnd_3508171 < baseStart_3508171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508202 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_3508202 : Nat := 118140960795 + 3508202 * 2 ^ 59
def prefixEnd_3508202 : Nat := 4983230072969 + 3 ^ 40 * 3508202 * 2
def baseEnd_3508202 : Nat := 1801393859064588377241079

theorem tailTrace_3508202 : CollatzResearch.WordTrace tailWord_3508202 prefixEnd_3508202 1801393859064588377241079 := by
  unfold tailWord_3508202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31988659709097695511421715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85303092557593854697124573 31988659709097695511421715)
  ·
    refine ⟨47982989563646543267132573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31988659709097695511421715 47982989563646543267132573)
    ·
      refine ⟨17993621086367453725174715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47982989563646543267132573 17993621086367453725174715)
      ·
        refine ⟨26990431629551180587762073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17993621086367453725174715 26990431629551180587762073)
        ·
          refine ⟨20242823722163385440821555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26990431629551180587762073 20242823722163385440821555)
          ·
            refine ⟨30364235583245078161232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20242823722163385440821555 30364235583245078161232333)
            ·
              refine ⟨11386588343716904310462125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30364235583245078161232333 11386588343716904310462125)
              ·
                refine ⟨4269970628893839116423297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11386588343716904310462125 4269970628893839116423297)
                ·
                  refine ⟨3202477971670379337317473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4269970628893839116423297 3202477971670379337317473)
                  ·
                    refine ⟨2401858478752784502988105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3202477971670379337317473 2401858478752784502988105)
                    ·
                      refine ⟨1801393859064588377241079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401858478752784502988105 1801393859064588377241079)
                      ·
                        rfl

theorem cell23_3508202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_3508202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508202 prefixEnd_3508202 := by exact prefixLift 3508202
  have htrace : WordTrace (prefixWord ++ tailWord_3508202) baseStart_3508202 baseEnd_3508202 := by
    simpa [prefixWord, tailWord_3508202, baseEnd_3508202] using wordTrace_append hprefix tailTrace_3508202
  have hstable : (prefixWord ++ tailWord_3508202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508202).length < 2 ^ (prefixWord ++ tailWord_3508202).sum := by decide
  have hdescent : baseEnd_3508202 < baseStart_3508202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508221 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_3508221 : Nat := 118140960795 + 3508221 * 2 ^ 59
def prefixEnd_3508221 : Nat := 4983230072969 + 3 ^ 40 * 3508221 * 2
def baseEnd_3508221 : Nat := 600467871732341267634497

theorem tailTrace_3508221 : CollatzResearch.WordTrace tailWord_3508221 prefixEnd_3508221 600467871732341267634497 := by
  unfold tailWord_3508221
  simp only [CollatzResearch.WordTrace]
  refine ⟨127955331823321948290628517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85303554548881298860419011 127955331823321948290628517)
  ·
    refine ⟨23991624716872865304492847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127955331823321948290628517 23991624716872865304492847)
    ·
      refine ⟨35987437075309297956739271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23991624716872865304492847 35987437075309297956739271)
      ·
        refine ⟨53981155612963946935108907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35987437075309297956739271 53981155612963946935108907)
        ·
          refine ⟨80971733419445920402663361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53981155612963946935108907 80971733419445920402663361)
          ·
            refine ⟨60728800064584440301997521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80971733419445920402663361 60728800064584440301997521)
            ·
              refine ⟨45546600048438330226498141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60728800064584440301997521 45546600048438330226498141)
              ·
                refine ⟨17079975018164373834936803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45546600048438330226498141 17079975018164373834936803)
                ·
                  refine ⟨25619962527246560752405205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17079975018164373834936803 25619962527246560752405205)
                  ·
                    refine ⟨600467871732341267634497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25619962527246560752405205 600467871732341267634497)
                    ·
                      rfl

theorem cell23_3508221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_3508221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508221 prefixEnd_3508221 := by exact prefixLift 3508221
  have htrace : WordTrace (prefixWord ++ tailWord_3508221) baseStart_3508221 baseEnd_3508221 := by
    simpa [prefixWord, tailWord_3508221, baseEnd_3508221] using wordTrace_append hprefix tailTrace_3508221
  have hstable : (prefixWord ++ tailWord_3508221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508221).length < 2 ^ (prefixWord ++ tailWord_3508221).sum := by decide
  have hdescent : baseEnd_3508221 < baseStart_3508221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508238 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3508238 : Nat := 118140960795 + 3508238 * 2 ^ 59
def prefixEnd_3508238 : Nat := 4983230072969 + 3 ^ 40 * 3508238 * 2
def baseEnd_3508238 : Nat := 600470781456050078796971

theorem tailTrace_3508238 : CollatzResearch.WordTrace tailWord_3508238 prefixEnd_3508238 600470781456050078796971 := by
  unfold tailWord_3508238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994493983032545024249671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85303967909506906795998245 15994493983032545024249671)
  ·
    refine ⟨23991740974548817536374507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15994493983032545024249671 23991740974548817536374507)
    ·
      refine ⟨35987611461823226304561761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23991740974548817536374507 35987611461823226304561761)
      ·
        refine ⟨26990708596367419728421321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35987611461823226304561761 26990708596367419728421321)
        ·
          refine ⟨20243031447275564796315991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26990708596367419728421321 20243031447275564796315991)
          ·
            refine ⟨30364547170913347194473987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20243031447275564796315991 30364547170913347194473987)
            ·
              refine ⟨45546820756370020791710981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30364547170913347194473987 45546820756370020791710981)
              ·
                refine ⟨8540028891819378898445809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45546820756370020791710981 8540028891819378898445809)
                ·
                  refine ⟨6405021668864534173834357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8540028891819378898445809 6405021668864534173834357)
                  ·
                    refine ⟨600470781456050078796971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6405021668864534173834357 600470781456050078796971)
                    ·
                      rfl

theorem cell23_3508238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3508238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508238 prefixEnd_3508238 := by exact prefixLift 3508238
  have htrace : WordTrace (prefixWord ++ tailWord_3508238) baseStart_3508238 baseEnd_3508238 := by
    simpa [prefixWord, tailWord_3508238, baseEnd_3508238] using wordTrace_append hprefix tailTrace_3508238
  have hstable : (prefixWord ++ tailWord_3508238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508238).length < 2 ^ (prefixWord ++ tailWord_3508238).sum := by decide
  have hdescent : baseEnd_3508238 < baseStart_3508238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508241 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3508241 : Nat := 118140960795 + 3508241 * 2 ^ 59
def prefixEnd_3508241 : Nat := 4983230072969 + 3 ^ 40 * 3508241 * 2
def baseEnd_3508241 : Nat := 1801413884810113724653399

theorem tailTrace_3508241 : CollatzResearch.WordTrace tailWord_3508241 prefixEnd_3508241 1801413884810113724653399 := by
  unfold tailWord_3508241
  simp only [CollatzResearch.WordTrace]
  refine ⟨127956061283249491706356577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85304040855499661137571051 127956061283249491706356577)
  ·
    refine ⟨95967045962437118779767433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127956061283249491706356577 95967045962437118779767433)
    ·
      refine ⟨71975284471827839084825575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95967045962437118779767433 71975284471827839084825575)
      ·
        refine ⟨107962926707741758627238363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71975284471827839084825575 107962926707741758627238363)
        ·
          refine ⟨161944390061612637940857545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107962926707741758627238363 161944390061612637940857545)
          ·
            refine ⟨121458292546209478455643159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161944390061612637940857545 121458292546209478455643159)
            ·
              refine ⟨182187438819314217683464739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121458292546209478455643159 182187438819314217683464739)
              ·
                refine ⟨273281158228971326525197109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182187438819314217683464739 273281158228971326525197109)
                ·
                  refine ⟨25620108583966061861737229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273281158228971326525197109 25620108583966061861737229)
                  ·
                    refine ⟨9607540718987273198151461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25620108583966061861737229 9607540718987273198151461)
                    ·
                      refine ⟨1801413884810113724653399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9607540718987273198151461 1801413884810113724653399)
                      ·
                        rfl

theorem cell23_3508241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3508241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508241 prefixEnd_3508241 := by exact prefixLift 3508241
  have htrace : WordTrace (prefixWord ++ tailWord_3508241) baseStart_3508241 baseEnd_3508241 := by
    simpa [prefixWord, tailWord_3508241, baseEnd_3508241] using wordTrace_append hprefix tailTrace_3508241
  have hstable : (prefixWord ++ tailWord_3508241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508241).length < 2 ^ (prefixWord ++ tailWord_3508241).sum := by decide
  have hdescent : baseEnd_3508241 < baseStart_3508241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508258 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3508258 : Nat := 118140960795 + 3508258 * 2 ^ 59
def prefixEnd_3508258 : Nat := 4983230072969 + 3 ^ 40 * 3508258 * 2
def baseEnd_3508258 : Nat := 1801422613981240158140821

theorem tailTrace_3508258 : CollatzResearch.WordTrace tailWord_3508258 prefixEnd_3508258 1801422613981240158140821 := by
  unfold tailWord_3508258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31989170331046975902431357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85304454216125269073150285 31989170331046975902431357)
  ·
    refine ⟨11995938874142615963411759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31989170331046975902431357 11995938874142615963411759)
    ·
      refine ⟨17993908311213923945117639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11995938874142615963411759 17993908311213923945117639)
      ·
        refine ⟨26990862466820885917676459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17993908311213923945117639 26990862466820885917676459)
        ·
          refine ⟨40486293700231328876514689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26990862466820885917676459 40486293700231328876514689)
          ·
            refine ⟨30364720275173496657386017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40486293700231328876514689 30364720275173496657386017)
            ·
              refine ⟨22773540206380122493039513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30364720275173496657386017 22773540206380122493039513)
              ·
                refine ⟨17080155154785091869779635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22773540206380122493039513 17080155154785091869779635)
                ·
                  refine ⟨25620232732177637804669453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17080155154785091869779635 25620232732177637804669453)
                  ·
                    refine ⟨9607587274566614176751045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25620232732177637804669453 9607587274566614176751045)
                    ·
                      refine ⟨1801422613981240158140821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9607587274566614176751045 1801422613981240158140821)
                      ·
                        rfl

theorem cell23_3508258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3508258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508258 prefixEnd_3508258 := by exact prefixLift 3508258
  have htrace : WordTrace (prefixWord ++ tailWord_3508258) baseStart_3508258 baseEnd_3508258 := by
    simpa [prefixWord, tailWord_3508258, baseEnd_3508258] using wordTrace_append hprefix tailTrace_3508258
  have hstable : (prefixWord ++ tailWord_3508258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508258).length < 2 ^ (prefixWord ++ tailWord_3508258).sum := by decide
  have hdescent : baseEnd_3508258 < baseStart_3508258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508271 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_3508271 : Nat := 118140960795 + 3508271 * 2 ^ 59
def prefixEnd_3508271 : Nat := 4983230072969 + 3 ^ 40 * 3508271 * 2
def baseEnd_3508271 : Nat := 1801429289229748607278261

theorem tailTrace_3508271 : CollatzResearch.WordTrace tailWord_3508271 prefixEnd_3508271 1801429289229748607278261 := by
  unfold tailWord_3508271
  simp only [CollatzResearch.WordTrace]
  refine ⟨127957155473140806829948667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85304770315427204553299111 127957155473140806829948667)
  ·
    refine ⟨191935733209711210244923001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127957155473140806829948667 191935733209711210244923001)
    ·
      refine ⟨143951799907283407683692251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191935733209711210244923001 143951799907283407683692251)
      ·
        refine ⟨215927699860925111525538377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143951799907283407683692251 215927699860925111525538377)
        ·
          refine ⟨161945774895693833644153783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215927699860925111525538377 161945774895693833644153783)
          ·
            refine ⟨242918662343540750466230675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161945774895693833644153783 242918662343540750466230675)
            ·
              refine ⟨364377993515311125699346013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242918662343540750466230675 364377993515311125699346013)
              ·
                refine ⟨136641747568241672137254755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364377993515311125699346013 136641747568241672137254755)
                ·
                  refine ⟨204962621352362508205882133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136641747568241672137254755 204962621352362508205882133)
                  ·
                    refine ⟨9607622875891992572150725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204962621352362508205882133 9607622875891992572150725)
                    ·
                      refine ⟨1801429289229748607278261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9607622875891992572150725 1801429289229748607278261)
                      ·
                        rfl

theorem cell23_3508271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_3508271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508271 prefixEnd_3508271 := by exact prefixLift 3508271
  have htrace : WordTrace (prefixWord ++ tailWord_3508271) baseStart_3508271 baseEnd_3508271 := by
    simpa [prefixWord, tailWord_3508271, baseEnd_3508271] using wordTrace_append hprefix tailTrace_3508271
  have hstable : (prefixWord ++ tailWord_3508271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508271).length < 2 ^ (prefixWord ++ tailWord_3508271).sum := by decide
  have hdescent : baseEnd_3508271 < baseStart_3508271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508302 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3508302 : Nat := 118140960795 + 3508302 * 2 ^ 59
def prefixEnd_3508302 : Nat := 4983230072969 + 3 ^ 40 * 3508302 * 2
def baseEnd_3508302 : Nat := 600481735710012661996873

theorem tailTrace_3508302 : CollatzResearch.WordTrace tailWord_3508302 prefixEnd_3508302 600481735710012661996873 := by
  unfold tailWord_3508302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994785767003562390540895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85305524090685666082884773 15994785767003562390540895)
  ·
    refine ⟨23992178650505343585811343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15994785767003562390540895 23992178650505343585811343)
    ·
      refine ⟨35988267975758015378717015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23992178650505343585811343 35988267975758015378717015)
      ·
        refine ⟨53982401963637023068075523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35988267975758015378717015 53982401963637023068075523)
        ·
          refine ⟨80973602945455534602113285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53982401963637023068075523 80973602945455534602113285)
          ·
            refine ⟨15182550552272912737896241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80973602945455534602113285 15182550552272912737896241)
            ·
              refine ⟨11386912914204684553422181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15182550552272912737896241 11386912914204684553422181)
              ·
                refine ⟨2135046171413378353766659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11386912914204684553422181 2135046171413378353766659)
                ·
                  refine ⟨3202569257120067530649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135046171413378353766659 3202569257120067530649989)
                  ·
                    refine ⟨600481735710012661996873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3202569257120067530649989 600481735710012661996873)
                    ·
                      rfl

theorem cell23_3508302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3508302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508302 prefixEnd_3508302 := by exact prefixLift 3508302
  have htrace : WordTrace (prefixWord ++ tailWord_3508302) baseStart_3508302 baseEnd_3508302 := by
    simpa [prefixWord, tailWord_3508302, baseEnd_3508302] using wordTrace_append hprefix tailTrace_3508302
  have hstable : (prefixWord ++ tailWord_3508302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508302).length < 2 ^ (prefixWord ++ tailWord_3508302).sum := by decide
  have hdescent : baseEnd_3508302 < baseStart_3508302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508335 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 5, 2]
def baseStart_3508335 : Nat := 118140960795 + 3508335 * 2 ^ 59
def prefixEnd_3508335 : Nat := 4983230072969 + 3 ^ 40 * 3508335 * 2
def baseEnd_3508335 : Nat := 1801462151991636356877967

theorem tailTrace_3508335 : CollatzResearch.WordTrace tailWord_3508335 prefixEnd_3508335 1801462151991636356877967 := by
  unfold tailWord_3508335
  simp only [CollatzResearch.WordTrace]
  refine ⟨127959489744908945760278459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85306326496605963840185639 127959489744908945760278459)
  ·
    refine ⟨191939234617363418640417689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127959489744908945760278459 191939234617363418640417689)
    ·
      refine ⟨143954425963022563980313267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191939234617363418640417689 143954425963022563980313267)
      ·
        refine ⟨215931638944533845970469901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143954425963022563980313267 215931638944533845970469901)
        ·
          refine ⟨80974364604200192238926213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215931638944533845970469901 80974364604200192238926213)
          ·
            refine ⟨15182693363287536044798665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80974364604200192238926213 15182693363287536044798665)
            ·
              refine ⟨11387020022465652033598999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15182693363287536044798665 11387020022465652033598999)
              ·
                refine ⟨17080530033698478050398499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387020022465652033598999 17080530033698478050398499)
                ·
                  refine ⟨25620795050547717075597749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17080530033698478050398499 25620795050547717075597749)
                  ·
                    refine ⟨2401949535988848475837289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25620795050547717075597749 2401949535988848475837289)
                    ·
                      refine ⟨1801462151991636356877967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401949535988848475837289 1801462151991636356877967)
                      ·
                        rfl

theorem cell23_3508335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 5, 2].length) (baseStart_3508335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508335 prefixEnd_3508335 := by exact prefixLift 3508335
  have htrace : WordTrace (prefixWord ++ tailWord_3508335) baseStart_3508335 baseEnd_3508335 := by
    simpa [prefixWord, tailWord_3508335, baseEnd_3508335] using wordTrace_append hprefix tailTrace_3508335
  have hstable : (prefixWord ++ tailWord_3508335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508335).length < 2 ^ (prefixWord ++ tailWord_3508335).sum := by decide
  have hdescent : baseEnd_3508335 < baseStart_3508335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508345 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_3508345 : Nat := 118140960795 + 3508345 * 2 ^ 59
def prefixEnd_3508345 : Nat := 4983230072969 + 3 ^ 40 * 3508345 * 2
def baseEnd_3508345 : Nat := 600489095599393772584307

theorem tailTrace_3508345 : CollatzResearch.WordTrace tailWord_3508345 prefixEnd_3508345 600489095599393772584307 := by
  unfold tailWord_3508345
  simp only [CollatzResearch.WordTrace]
  refine ⟨127959854474872717468142489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85306569649915144978761659 127959854474872717468142489)
  ·
    refine ⟨95969890856154538101106867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127959854474872717468142489 95969890856154538101106867)
    ·
      refine ⟨143954836284231807151660301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95969890856154538101106867 143954836284231807151660301)
      ·
        refine ⟨53983063606586927681872613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143954836284231807151660301 53983063606586927681872613)
        ·
          refine ⟨10121824426235048940351115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53983063606586927681872613 10121824426235048940351115)
          ·
            refine ⟨15182736639352573410526673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10121824426235048940351115 15182736639352573410526673)
            ·
              refine ⟨11387052479514430057895005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15182736639352573410526673 11387052479514430057895005)
              ·
                refine ⟨4270144679817911271710627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11387052479514430057895005 4270144679817911271710627)
                ·
                  refine ⟨6405217019726866907565941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270144679817911271710627 6405217019726866907565941)
                  ·
                    refine ⟨600489095599393772584307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6405217019726866907565941 600489095599393772584307)
                    ·
                      rfl

theorem cell23_3508345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_3508345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508345 prefixEnd_3508345 := by exact prefixLift 3508345
  have htrace : WordTrace (prefixWord ++ tailWord_3508345) baseStart_3508345 baseEnd_3508345 := by
    simpa [prefixWord, tailWord_3508345, baseEnd_3508345] using wordTrace_append hprefix tailTrace_3508345
  have hstable : (prefixWord ++ tailWord_3508345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508345).length < 2 ^ (prefixWord ++ tailWord_3508345).sum := by decide
  have hdescent : baseEnd_3508345 < baseStart_3508345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508368 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_3508368 : Nat := 118140960795 + 3508368 * 2 ^ 59
def prefixEnd_3508368 : Nat := 4983230072969 + 3 ^ 40 * 3508368 * 2
def baseEnd_3508368 : Nat := 1801479096853234727765315

theorem tailTrace_3508368 : CollatzResearch.WordTrace tailWord_3508368 prefixEnd_3508368 1801479096853234727765315 := by
  unfold tailWord_3508368
  simp only [CollatzResearch.WordTrace]
  refine ⟨63980346676894696198114879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85307128902526261597486505 63980346676894696198114879)
  ·
    refine ⟨95970520015342044297172319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63980346676894696198114879 95970520015342044297172319)
    ·
      refine ⟨143955780023013066445758479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95970520015342044297172319 143955780023013066445758479)
      ·
        refine ⟨215933670034519599668637719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143955780023013066445758479 215933670034519599668637719)
        ·
          refine ⟨323900505051779399502956579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215933670034519599668637719 323900505051779399502956579)
          ·
            refine ⟨485850757577669099254434869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323900505051779399502956579 485850757577669099254434869)
            ·
              refine ⟨45548508522906478055103269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485850757577669099254434869 45548508522906478055103269)
              ·
                refine ⟨8540345348044964635331863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45548508522906478055103269 8540345348044964635331863)
                ·
                  refine ⟨12810518022067446952997795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540345348044964635331863 12810518022067446952997795)
                  ·
                    refine ⟨19215777033101170429496693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12810518022067446952997795 19215777033101170429496693)
                    ·
                      refine ⟨1801479096853234727765315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19215777033101170429496693 1801479096853234727765315)
                      ·
                        rfl

theorem cell23_3508368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_3508368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508368 prefixEnd_3508368 := by exact prefixLift 3508368
  have htrace : WordTrace (prefixWord ++ tailWord_3508368) baseStart_3508368 baseEnd_3508368 := by
    simpa [prefixWord, tailWord_3508368, baseEnd_3508368] using wordTrace_append hprefix tailTrace_3508368
  have hstable : (prefixWord ++ tailWord_3508368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508368).length < 2 ^ (prefixWord ++ tailWord_3508368).sum := by decide
  have hdescent : baseEnd_3508368 < baseStart_3508368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508399 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 1, 2, 2]
def baseStart_3508399 : Nat := 118140960795 + 3508399 * 2 ^ 59
def prefixEnd_3508399 : Nat := 4983230072969 + 3 ^ 40 * 3508399 * 2
def baseEnd_3508399 : Nat := 1801495014753524106477673

theorem tailTrace_3508399 : CollatzResearch.WordTrace tailWord_3508399 prefixEnd_3508399 1801495014753524106477673 := by
  unfold tailWord_3508399
  simp only [CollatzResearch.WordTrace]
  refine ⟨127961824016677084690608251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85307882677784723127072167 127961824016677084690608251)
  ·
    refine ⟨191942736025015627035912377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127961824016677084690608251 191942736025015627035912377)
    ·
      refine ⟨143957052018761720276934283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191942736025015627035912377 143957052018761720276934283)
      ·
        refine ⟨215935578028142580415401425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143957052018761720276934283 215935578028142580415401425)
        ·
          refine ⟨161951683521106935311551069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215935578028142580415401425 161951683521106935311551069)
          ·
            refine ⟨60731881320415100741831651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161951683521106935311551069 60731881320415100741831651)
            ·
              refine ⟨91097821980622651112747477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60731881320415100741831651 91097821980622651112747477)
              ·
                refine ⟨2135105202670843385455019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91097821980622651112747477 2135105202670843385455019)
                ·
                  refine ⟨3202657804006265078182529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135105202670843385455019 3202657804006265078182529)
                  ·
                    refine ⟨2401993353004698808636897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3202657804006265078182529 2401993353004698808636897)
                    ·
                      refine ⟨1801495014753524106477673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2401993353004698808636897 1801495014753524106477673)
                      ·
                        rfl

theorem cell23_3508399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 2, 2].length) (baseStart_3508399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508399 prefixEnd_3508399 := by exact prefixLift 3508399
  have htrace : WordTrace (prefixWord ++ tailWord_3508399) baseStart_3508399 baseEnd_3508399 := by
    simpa [prefixWord, tailWord_3508399, baseEnd_3508399] using wordTrace_append hprefix tailTrace_3508399
  have hstable : (prefixWord ++ tailWord_3508399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508399).length < 2 ^ (prefixWord ++ tailWord_3508399).sum := by decide
  have hdescent : baseEnd_3508399 < baseStart_3508399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508405 : List Nat := [1, 3, 3, 4, 1, 11]
def baseStart_3508405 : Nat := 118140960795 + 3508405 * 2 ^ 59
def prefixEnd_3508405 : Nat := 4983230072969 + 3 ^ 40 * 3508405 * 2
def baseEnd_3508405 : Nat := 7413572410030662893015

theorem tailTrace_3508405 : CollatzResearch.WordTrace tailWord_3508405 prefixEnd_3508405 7413572410030662893015 := by
  unfold tailWord_3508405
  simp only [CollatzResearch.WordTrace]
  refine ⟨127962042854655347715326669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85308028569770231810217779 127962042854655347715326669)
  ·
    refine ⟨47985766070495755393247501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127962042854655347715326669 47985766070495755393247501)
    ·
      refine ⟨17994662276435908272467813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47985766070495755393247501 17994662276435908272467813)
      ·
        refine ⟨3373999176831732801087715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17994662276435908272467813 3373999176831732801087715)
        ·
          refine ⟨5060998765247599201631573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373999176831732801087715 5060998765247599201631573)
          ·
            refine ⟨7413572410030662893015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5060998765247599201631573 7413572410030662893015)
            ·
              rfl

theorem cell23_3508405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 11].length) (baseStart_3508405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508405 prefixEnd_3508405 := by exact prefixLift 3508405
  have htrace : WordTrace (prefixWord ++ tailWord_3508405) baseStart_3508405 baseEnd_3508405 := by
    simpa [prefixWord, tailWord_3508405, baseEnd_3508405] using wordTrace_append hprefix tailTrace_3508405
  have hstable : (prefixWord ++ tailWord_3508405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508405).length < 2 ^ (prefixWord ++ tailWord_3508405).sum := by decide
  have hdescent : baseEnd_3508405 < baseStart_3508405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508416 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 1, 2, 2]
def baseStart_3508416 : Nat := 118140960795 + 3508416 * 2 ^ 59
def prefixEnd_3508416 : Nat := 4983230072969 + 3 ^ 40 * 3508416 * 2
def baseEnd_3508416 : Nat := 1801503743924650539965095

theorem tailTrace_3508416 : CollatzResearch.WordTrace tailWord_3508416 prefixEnd_3508416 1801503743924650539965095 := by
  unfold tailWord_3508416
  simp only [CollatzResearch.WordTrace]
  refine ⟨63981222028807748296988551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85308296038410331062651401 63981222028807748296988551)
  ·
    refine ⟨95971833043211622445482827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63981222028807748296988551 95971833043211622445482827)
    ·
      refine ⟨143957749564817433668224241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95971833043211622445482827 143957749564817433668224241)
      ·
        refine ⟨107968312173613075251168181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143957749564817433668224241 107968312173613075251168181)
        ·
          refine ⟨10122029266276225804797017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107968312173613075251168181 10122029266276225804797017)
          ·
            refine ⟨7591521949707169353597763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10122029266276225804797017 7591521949707169353597763)
            ·
              refine ⟨11387282924560754030396645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7591521949707169353597763 11387282924560754030396645)
              ·
                refine ⟨2135115548355141380699371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11387282924560754030396645 2135115548355141380699371)
                ·
                  refine ⟨3202673322532712071049057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135115548355141380699371 3202673322532712071049057)
                  ·
                    refine ⟨2402004991899534053286793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3202673322532712071049057 2402004991899534053286793)
                    ·
                      refine ⟨1801503743924650539965095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402004991899534053286793 1801503743924650539965095)
                      ·
                        rfl

theorem cell23_3508416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_3508416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508416 prefixEnd_3508416 := by exact prefixLift 3508416
  have htrace : WordTrace (prefixWord ++ tailWord_3508416) baseStart_3508416 baseEnd_3508416 := by
    simpa [prefixWord, tailWord_3508416, baseEnd_3508416] using wordTrace_append hprefix tailTrace_3508416
  have hstable : (prefixWord ++ tailWord_3508416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508416).length < 2 ^ (prefixWord ++ tailWord_3508416).sum := by decide
  have hdescent : baseEnd_3508416 < baseStart_3508416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508442 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_3508442 : Nat := 118140960795 + 3508442 * 2 ^ 59
def prefixEnd_3508442 : Nat := 4983230072969 + 3 ^ 40 * 3508442 * 2
def baseEnd_3508442 : Nat := 1801517094421667438239975

theorem tailTrace_3508442 : CollatzResearch.WordTrace tailWord_3508442 prefixEnd_3508442 1801517094421667438239975 := by
  unfold tailWord_3508442
  simp only [CollatzResearch.WordTrace]
  refine ⟨31990848088880325758605895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85308928237014202022949053 31990848088880325758605895)
  ·
    refine ⟨47986272133320488637908843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31990848088880325758605895 47986272133320488637908843)
    ·
      refine ⟨71979408199980732956863265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47986272133320488637908843 71979408199980732956863265)
      ·
        refine ⟨53984556149985549717647449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71979408199980732956863265 53984556149985549717647449)
        ·
          refine ⟨40488417112489162288235587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53984556149985549717647449 40488417112489162288235587)
          ·
            refine ⟨60732625668733743432353381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40488417112489162288235587 60732625668733743432353381)
            ·
              refine ⟨11387367312887576893566259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60732625668733743432353381 11387367312887576893566259)
              ·
                refine ⟨17081050969331365340349389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387367312887576893566259 17081050969331365340349389)
                ·
                  refine ⟨6405394113499262002631021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17081050969331365340349389 6405394113499262002631021)
                  ·
                    refine ⟨2402022792562223250986633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6405394113499262002631021 2402022792562223250986633)
                    ·
                      refine ⟨1801517094421667438239975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402022792562223250986633 1801517094421667438239975)
                      ·
                        rfl

theorem cell23_3508442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_3508442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508442 prefixEnd_3508442 := by exact prefixLift 3508442
  have htrace : WordTrace (prefixWord ++ tailWord_3508442) baseStart_3508442 baseEnd_3508442 := by
    simpa [prefixWord, tailWord_3508442, baseEnd_3508442] using wordTrace_append hprefix tailTrace_3508442
  have hstable : (prefixWord ++ tailWord_3508442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508442).length < 2 ^ (prefixWord ++ tailWord_3508442).sum := by decide
  have hdescent : baseEnd_3508442 < baseStart_3508442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508448 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_3508448 : Nat := 118140960795 + 3508448 * 2 ^ 59
def prefixEnd_3508448 : Nat := 4983230072969 + 3 ^ 40 * 3508448 * 2
def baseEnd_3508448 : Nat := 600506725101864804921649

theorem tailTrace_3508448 : CollatzResearch.WordTrace tailWord_3508448 prefixEnd_3508448 600506725101864804921649 := by
  unfold tailWord_3508448
  simp only [CollatzResearch.WordTrace]
  refine ⟨63981805596749783029570999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85309074128999710706094665 63981805596749783029570999)
  ·
    refine ⟨95972708395124674544356499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63981805596749783029570999 95972708395124674544356499)
    ·
      refine ⟨143959062592687011816534749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95972708395124674544356499 143959062592687011816534749)
      ·
        refine ⟨53984648472257629431200531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143959062592687011816534749 53984648472257629431200531)
        ·
          refine ⟨80976972708386444146800797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53984648472257629431200531 80976972708386444146800797)
          ·
            refine ⟨30366364765644916555050299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80976972708386444146800797 30366364765644916555050299)
            ·
              refine ⟨45549547148467374832575449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30366364765644916555050299 45549547148467374832575449)
              ·
                refine ⟨34162160361350531124431587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45549547148467374832575449 34162160361350531124431587)
                ·
                  refine ⟨51243240542025796686647381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34162160361350531124431587 51243240542025796686647381)
                  ·
                    refine ⟨600506725101864804921649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51243240542025796686647381 600506725101864804921649)
                    ·
                      rfl

theorem cell23_3508448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_3508448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508448 prefixEnd_3508448 := by exact prefixLift 3508448
  have htrace : WordTrace (prefixWord ++ tailWord_3508448) baseStart_3508448 baseEnd_3508448 := by
    simpa [prefixWord, tailWord_3508448, baseEnd_3508448] using wordTrace_append hprefix tailTrace_3508448
  have hstable : (prefixWord ++ tailWord_3508448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508448).length < 2 ^ (prefixWord ++ tailWord_3508448).sum := by decide
  have hdescent : baseEnd_3508448 < baseStart_3508448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508450 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3508450 : Nat := 118140960795 + 3508450 * 2 ^ 59
def prefixEnd_3508450 : Nat := 4983230072969 + 3 ^ 40 * 3508450 * 2
def baseEnd_3508450 : Nat := 1801521202266903406939939

theorem tailTrace_3508450 : CollatzResearch.WordTrace tailWord_3508450 prefixEnd_3508450 1801521202266903406939939 := by
  unfold tailWord_3508450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31990921034873080100178701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85309122759661546933809869 31990921034873080100178701)
  ·
    refine ⟨11996595388077405037567013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31990921034873080100178701 11996595388077405037567013)
    ·
      refine ⟨2249361635264513444543815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11996595388077405037567013 2249361635264513444543815)
      ·
        refine ⟨3374042452896770166815723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249361635264513444543815 3374042452896770166815723)
        ·
          refine ⟨5061063679345155250223585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374042452896770166815723 5061063679345155250223585)
          ·
            refine ⟨3795797759508866437667689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061063679345155250223585 3795797759508866437667689)
            ·
              refine ⟨2846848319631649828250767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3795797759508866437667689 2846848319631649828250767)
              ·
                refine ⟨4270272479447474742376151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846848319631649828250767 4270272479447474742376151)
                ·
                  refine ⟨6405408719171212113564227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270272479447474742376151 6405408719171212113564227)
                  ·
                    refine ⟨9608113078756818170346341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405408719171212113564227 9608113078756818170346341)
                    ·
                      refine ⟨1801521202266903406939939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9608113078756818170346341 1801521202266903406939939)
                      ·
                        rfl

theorem cell23_3508450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3508450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508450 prefixEnd_3508450 := by exact prefixLift 3508450
  have htrace : WordTrace (prefixWord ++ tailWord_3508450) baseStart_3508450 baseEnd_3508450 := by
    simpa [prefixWord, tailWord_3508450, baseEnd_3508450] using wordTrace_append hprefix tailTrace_3508450
  have hstable : (prefixWord ++ tailWord_3508450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508450).length < 2 ^ (prefixWord ++ tailWord_3508450).sum := by decide
  have hdescent : baseEnd_3508450 < baseStart_3508450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508466 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3508466 : Nat := 118140960795 + 3508466 * 2 ^ 59
def prefixEnd_3508466 : Nat := 4983230072969 + 3 ^ 40 * 3508466 * 2
def baseEnd_3508466 : Nat := 1801529417957375344339865

theorem tailTrace_3508466 : CollatzResearch.WordTrace tailWord_3508466 prefixEnd_3508466 1801529417957375344339865 := by
  unfold tailWord_3508466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991066926858588783324313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85309511804956236755531501 31991066926858588783324313)
  ·
    refine ⟨23993300195143941587493235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31991066926858588783324313 23993300195143941587493235)
    ·
      refine ⟨35989950292715912381239853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23993300195143941587493235 35989950292715912381239853)
      ·
        refine ⟨13496231359768467142964945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35989950292715912381239853 13496231359768467142964945)
        ·
          refine ⟨10122173519826350357223709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13496231359768467142964945 10122173519826350357223709)
          ·
            refine ⟨3795815069934881383958891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10122173519826350357223709 3795815069934881383958891)
            ·
              refine ⟨5693722604902322075938337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795815069934881383958891 5693722604902322075938337)
              ·
                refine ⟨4270291953676741556953753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693722604902322075938337 4270291953676741556953753)
                ·
                  refine ⟨3202718965257556167715315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270291953676741556953753 3202718965257556167715315)
                  ·
                    refine ⟨4804078447886334251572973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3202718965257556167715315 4804078447886334251572973)
                    ·
                      refine ⟨1801529417957375344339865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4804078447886334251572973 1801529417957375344339865)
                      ·
                        rfl

theorem cell23_3508466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3508466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508466 prefixEnd_3508466 := by exact prefixLift 3508466
  have htrace : WordTrace (prefixWord ++ tailWord_3508466) baseStart_3508466 baseEnd_3508466 := by
    simpa [prefixWord, tailWord_3508466, baseEnd_3508466] using wordTrace_append hprefix tailTrace_3508466
  have hstable : (prefixWord ++ tailWord_3508466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508466).length < 2 ^ (prefixWord ++ tailWord_3508466).sum := by decide
  have hdescent : baseEnd_3508466 < baseStart_3508466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508482 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3508482 : Nat := 118140960795 + 3508482 * 2 ^ 59
def prefixEnd_3508482 : Nat := 4983230072969 + 3 ^ 40 * 3508482 * 2
def baseEnd_3508482 : Nat := 600512544549282427246597

theorem tailTrace_3508482 : CollatzResearch.WordTrace tailWord_3508482 prefixEnd_3508482 600512544549282427246597 := by
  unfold tailWord_3508482
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991212818844097466469925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85309900850250926577253133 31991212818844097466469925)
  ·
    refine ⟨5998352403533268274963111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31991212818844097466469925 5998352403533268274963111)
    ·
      refine ⟨8997528605299902412444667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998352403533268274963111 8997528605299902412444667)
      ·
        refine ⟨13496292907949853618667001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8997528605299902412444667 13496292907949853618667001)
        ·
          refine ⟨10122219680962390214000251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13496292907949853618667001 10122219680962390214000251)
          ·
            refine ⟨15183329521443585321000377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122219680962390214000251 15183329521443585321000377)
            ·
              refine ⟨11387497141082688990750283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15183329521443585321000377 11387497141082688990750283)
              ·
                refine ⟨17081245711624033486125425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11387497141082688990750283 17081245711624033486125425)
                ·
                  refine ⟨12810934283718025114594069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17081245711624033486125425 12810934283718025114594069)
                  ·
                    refine ⟨600512544549282427246597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12810934283718025114594069 600512544549282427246597)
                    ·
                      rfl

theorem cell23_3508482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3508482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508482 prefixEnd_3508482 := by exact prefixLift 3508482
  have htrace : WordTrace (prefixWord ++ tailWord_3508482) baseStart_3508482 baseEnd_3508482 := by
    simpa [prefixWord, tailWord_3508482, baseEnd_3508482] using wordTrace_append hprefix tailTrace_3508482
  have hstable : (prefixWord ++ tailWord_3508482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508482).length < 2 ^ (prefixWord ++ tailWord_3508482).sum := by decide
  have hdescent : baseEnd_3508482 < baseStart_3508482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508489 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 1, 4, 2]
def baseStart_3508489 : Nat := 118140960795 + 3508489 * 2 ^ 59
def prefixEnd_3508489 : Nat := 4983230072969 + 3 ^ 40 * 3508489 * 2
def baseEnd_3508489 : Nat := 1801541228012428754352259

theorem tailTrace_3508489 : CollatzResearch.WordTrace tailWord_3508489 prefixEnd_3508489 1801541228012428754352259 := by
  unfold tailWord_3508489
  simp only [CollatzResearch.WordTrace]
  refine ⟨127965106586351030061384521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85310071057567353374256347 127965106586351030061384521)
  ·
    refine ⟨95973829939763272546038391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127965106586351030061384521 95973829939763272546038391)
    ·
      refine ⟨143960744909644908819057587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95973829939763272546038391 143960744909644908819057587)
      ·
        refine ⟨215941117364467363228586381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143960744909644908819057587 215941117364467363228586381)
        ·
          refine ⟨80977919011675261210719893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215941117364467363228586381 80977919011675261210719893)
          ·
            refine ⟨3795839953672277869252495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80977919011675261210719893 3795839953672277869252495)
            ·
              refine ⟨5693759930508416803878743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795839953672277869252495 5693759930508416803878743)
              ·
                refine ⟨8540639895762625205818115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693759930508416803878743 8540639895762625205818115)
                ·
                  refine ⟨12810959843643937808727173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540639895762625205818115 12810959843643937808727173)
                  ·
                    refine ⟨2402054970683238339136345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12810959843643937808727173 2402054970683238339136345)
                    ·
                      refine ⟨1801541228012428754352259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402054970683238339136345 1801541228012428754352259)
                      ·
                        rfl

theorem cell23_3508489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4, 2].length) (baseStart_3508489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508489 prefixEnd_3508489 := by exact prefixLift 3508489
  have htrace : WordTrace (prefixWord ++ tailWord_3508489) baseStart_3508489 baseEnd_3508489 := by
    simpa [prefixWord, tailWord_3508489, baseEnd_3508489] using wordTrace_append hprefix tailTrace_3508489
  have hstable : (prefixWord ++ tailWord_3508489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508489).length < 2 ^ (prefixWord ++ tailWord_3508489).sum := by decide
  have hdescent : baseEnd_3508489 < baseStart_3508489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508529 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 7]
def baseStart_3508529 : Nat := 118140960795 + 3508529 * 2 ^ 59
def prefixEnd_3508529 : Nat := 4983230072969 + 3 ^ 40 * 3508529 * 2
def baseEnd_3508529 : Nat := 200173529693178733094675

theorem tailTrace_3508529 : CollatzResearch.WordTrace tailWord_3508529 prefixEnd_3508529 200173529693178733094675 := by
  unfold tailWord_3508529
  simp only [CollatzResearch.WordTrace]
  refine ⟨127966565506206116892840641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85311043670804077928560427 127966565506206116892840641)
  ·
    refine ⟨95974924129654587669630481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127966565506206116892840641 95974924129654587669630481)
    ·
      refine ⟨71981193097240940752222861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95974924129654587669630481 71981193097240940752222861)
      ·
        refine ⟨26992947411465352782083573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71981193097240940752222861 26992947411465352782083573)
        ·
          refine ⟨2530588819824876823320335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26992947411465352782083573 2530588819824876823320335)
          ·
            refine ⟨3795883229737315234980503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530588819824876823320335 3795883229737315234980503)
            ·
              refine ⟨5693824844605972852470755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795883229737315234980503 5693824844605972852470755)
              ·
                refine ⟨8540737266908959278706133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5693824844605972852470755 8540737266908959278706133)
                ·
                  refine ⟨200173529693178733094675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8540737266908959278706133 200173529693178733094675)
                  ·
                    rfl

theorem cell23_3508529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 7].length) (baseStart_3508529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508529 prefixEnd_3508529 := by exact prefixLift 3508529
  have htrace : WordTrace (prefixWord ++ tailWord_3508529) baseStart_3508529 baseEnd_3508529 := by
    simpa [prefixWord, tailWord_3508529, baseEnd_3508529] using wordTrace_append hprefix tailTrace_3508529
  have hstable : (prefixWord ++ tailWord_3508529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508529).length < 2 ^ (prefixWord ++ tailWord_3508529).sum := by decide
  have hdescent : baseEnd_3508529 < baseStart_3508529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508562 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3508562 : Nat := 118140960795 + 3508562 * 2 ^ 59
def prefixEnd_3508562 : Nat := 4983230072969 + 3 ^ 40 * 3508562 * 2
def baseEnd_3508562 : Nat := 1801578712100206968739423

theorem tailTrace_3508562 : CollatzResearch.WordTrace tailWord_3508562 prefixEnd_3508562 1801578712100206968739423 := by
  unfold tailWord_3508562
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991942278771640882197985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85311846076724375685861293 31991942278771640882197985)
  ·
    refine ⟨23993956709078730661648489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31991942278771640882197985 23993956709078730661648489)
    ·
      refine ⟨17995467531809047996236367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23993956709078730661648489 17995467531809047996236367)
      ·
        refine ⟨26993201297713571994354551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17995467531809047996236367 26993201297713571994354551)
        ·
          refine ⟨40489801946570357991531827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26993201297713571994354551 40489801946570357991531827)
          ·
            refine ⟨60734702919855536987297741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40489801946570357991531827 60734702919855536987297741)
            ·
              refine ⟨22775513594945826370236653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60734702919855536987297741 22775513594945826370236653)
              ·
                refine ⟨8540817598104684888838745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22775513594945826370236653 8540817598104684888838745)
                ·
                  refine ⟨6405613198578513666629059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8540817598104684888838745 6405613198578513666629059)
                  ·
                    refine ⟨9608419797867770499943589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405613198578513666629059 9608419797867770499943589)
                    ·
                      refine ⟨1801578712100206968739423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9608419797867770499943589 1801578712100206968739423)
                      ·
                        rfl

theorem cell23_3508562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3508562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508562 prefixEnd_3508562 := by exact prefixLift 3508562
  have htrace : WordTrace (prefixWord ++ tailWord_3508562) baseStart_3508562 baseEnd_3508562 := by
    simpa [prefixWord, tailWord_3508562, baseEnd_3508562] using wordTrace_append hprefix tailTrace_3508562
  have hstable : (prefixWord ++ tailWord_3508562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508562).length < 2 ^ (prefixWord ++ tailWord_3508562).sum := by decide
  have hdescent : baseEnd_3508562 < baseStart_3508562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508574 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3508574 : Nat := 118140960795 + 3508574 * 2 ^ 59
def prefixEnd_3508574 : Nat := 4983230072969 + 3 ^ 40 * 3508574 * 2
def baseEnd_3508574 : Nat := 1801584873868060921789369

theorem tailTrace_3508574 : CollatzResearch.WordTrace tailWord_3508574 prefixEnd_3508574 1801584873868060921789369 := by
  unfold tailWord_3508574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996025848880386197278597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85312137860695393052152517 15996025848880386197278597)
  ·
    refine ⟨2999254846665072411989737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15996025848880386197278597 2999254846665072411989737)
    ·
      refine ⟨2249441134998804308992303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2999254846665072411989737 2249441134998804308992303)
      ·
        refine ⟨3374161702498206463488455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249441134998804308992303 3374161702498206463488455)
        ·
          refine ⟨5061242553747309695232683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374161702498206463488455 5061242553747309695232683)
          ·
            refine ⟨7591863830620964542849025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061242553747309695232683 7591863830620964542849025)
            ·
              refine ⟨5693897872965723407136769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591863830620964542849025 5693897872965723407136769)
              ·
                refine ⟨4270423404724292555352577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693897872965723407136769 4270423404724292555352577)
                ·
                  refine ⟨3202817553543219416514433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270423404724292555352577 3202817553543219416514433)
                  ·
                    refine ⟨2402113165157414562385825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3202817553543219416514433 2402113165157414562385825)
                    ·
                      refine ⟨1801584873868060921789369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402113165157414562385825 1801584873868060921789369)
                      ·
                        rfl

theorem cell23_3508574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3508574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508574 prefixEnd_3508574 := by exact prefixLift 3508574
  have htrace : WordTrace (prefixWord ++ tailWord_3508574) baseStart_3508574 baseEnd_3508574 := by
    simpa [prefixWord, tailWord_3508574, baseEnd_3508574] using wordTrace_append hprefix tailTrace_3508574
  have hstable : (prefixWord ++ tailWord_3508574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508574).length < 2 ^ (prefixWord ++ tailWord_3508574).sum := by decide
  have hdescent : baseEnd_3508574 < baseStart_3508574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508639 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3508639 : Nat := 118140960795 + 3508639 * 2 ^ 59
def prefixEnd_3508639 : Nat := 4983230072969 + 3 ^ 40 * 3508639 * 2
def baseEnd_3508639 : Nat := 1801618250110603167476569

theorem tailTrace_3508639 : CollatzResearch.WordTrace tailWord_3508639 prefixEnd_3508639 1801618250110603167476569 := by
  unfold tailWord_3508639
  simp only [CollatzResearch.WordTrace]
  refine ⟨127970577535807605679344971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85313718357205070452896647 127970577535807605679344971)
  ·
    refine ⟨191955866303711408519017457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127970577535807605679344971 191955866303711408519017457)
    ·
      refine ⟨143966899727783556389263093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191955866303711408519017457 143966899727783556389263093)
      ·
        refine ⟨13496896849479708411493415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143966899727783556389263093 13496896849479708411493415)
        ·
          refine ⟨20245345274219562617240123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13496896849479708411493415 20245345274219562617240123)
          ·
            refine ⟨30368017911329343925860185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20245345274219562617240123 30368017911329343925860185)
            ·
              refine ⟨22776013433497007944395139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30368017911329343925860185 22776013433497007944395139)
              ·
                refine ⟨34164020150245511916592709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22776013433497007944395139 34164020150245511916592709)
                ·
                  refine ⟨6405753778171033484361133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34164020150245511916592709 6405753778171033484361133)
                  ·
                    refine ⟨2402157666814137556635425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6405753778171033484361133 2402157666814137556635425)
                    ·
                      refine ⟨1801618250110603167476569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402157666814137556635425 1801618250110603167476569)
                      ·
                        rfl

theorem cell23_3508639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3508639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508639 prefixEnd_3508639 := by exact prefixLift 3508639
  have htrace : WordTrace (prefixWord ++ tailWord_3508639) baseStart_3508639 baseEnd_3508639 := by
    simpa [prefixWord, tailWord_3508639, baseEnd_3508639] using wordTrace_append hprefix tailTrace_3508639
  have hstable : (prefixWord ++ tailWord_3508639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508639).length < 2 ^ (prefixWord ++ tailWord_3508639).sum := by decide
  have hdescent : baseEnd_3508639 < baseStart_3508639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508669 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3508669 : Nat := 118140960795 + 3508669 * 2 ^ 59
def prefixEnd_3508669 : Nat := 4983230072969 + 3 ^ 40 * 3508669 * 2
def baseEnd_3508669 : Nat := 1801633654530238050101431

theorem tailTrace_3508669 : CollatzResearch.WordTrace tailWord_3508669 prefixEnd_3508669 1801633654530238050101431 := by
  unfold tailWord_3508669
  simp only [CollatzResearch.WordTrace]
  refine ⟨127971671725698920802937061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85314447817132613868624707 127971671725698920802937061)
  ·
    refine ⟨23994688448568547650550699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127971671725698920802937061 23994688448568547650550699)
    ·
      refine ⟨35992032672852821475826049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23994688448568547650550699 35992032672852821475826049)
      ·
        refine ⟨26994024504639616106869537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35992032672852821475826049 26994024504639616106869537)
        ·
          refine ⟨20245518378479712080152153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26994024504639616106869537 20245518378479712080152153)
          ·
            refine ⟨15184138783859784060114115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20245518378479712080152153 15184138783859784060114115)
            ·
              refine ⟨22776208175789676090171173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15184138783859784060114115 22776208175789676090171173)
              ·
                refine ⟨4270539032960564266907095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22776208175789676090171173 4270539032960564266907095)
                ·
                  refine ⟨6405808549440846400360643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270539032960564266907095 6405808549440846400360643)
                  ·
                    refine ⟨9608712824161269600540965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6405808549440846400360643 9608712824161269600540965)
                    ·
                      refine ⟨1801633654530238050101431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9608712824161269600540965 1801633654530238050101431)
                      ·
                        rfl

theorem cell23_3508669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3508669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508669 prefixEnd_3508669 := by exact prefixLift 3508669
  have htrace : WordTrace (prefixWord ++ tailWord_3508669) baseStart_3508669 baseEnd_3508669 := by
    simpa [prefixWord, tailWord_3508669, baseEnd_3508669] using wordTrace_append hprefix tailTrace_3508669
  have hstable : (prefixWord ++ tailWord_3508669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508669).length < 2 ^ (prefixWord ++ tailWord_3508669).sum := by decide
  have hdescent : baseEnd_3508669 < baseStart_3508669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508682 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3508682 : Nat := 118140960795 + 3508682 * 2 ^ 59
def prefixEnd_3508682 : Nat := 4983230072969 + 3 ^ 40 * 3508682 * 2
def baseEnd_3508682 : Nat := 1801640329778746499238871

theorem tailTrace_3508682 : CollatzResearch.WordTrace tailWord_3508682 prefixEnd_3508682 1801640329778746499238871 := by
  unfold tailWord_3508682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31993036468662956005790075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85314763916434549348773533 31993036468662956005790075)
  ·
    refine ⟨47989554702994434008685113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31993036468662956005790075 47989554702994434008685113)
    ·
      refine ⟨35992166027245825506513835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47989554702994434008685113 35992166027245825506513835)
      ·
        refine ⟨53988249040868738259770753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35992166027245825506513835 53988249040868738259770753)
        ·
          refine ⟨40491186780651553694828065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53988249040868738259770753 40491186780651553694828065)
          ·
            refine ⟨30368390085488665271121049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40491186780651553694828065 30368390085488665271121049)
            ·
              refine ⟨22776292564116498953340787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30368390085488665271121049 22776292564116498953340787)
              ·
                refine ⟨34164438846174748430011181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22776292564116498953340787 34164438846174748430011181)
                ·
                  refine ⟨12811664567315530661254193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34164438846174748430011181 12811664567315530661254193)
                  ·
                    refine ⟨9608748425486647995940645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12811664567315530661254193 9608748425486647995940645)
                    ·
                      refine ⟨1801640329778746499238871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9608748425486647995940645 1801640329778746499238871)
                      ·
                        rfl

theorem cell23_3508682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3508682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508682 prefixEnd_3508682 := by exact prefixLift 3508682
  have htrace : WordTrace (prefixWord ++ tailWord_3508682) baseStart_3508682 baseEnd_3508682 := by
    simpa [prefixWord, tailWord_3508682, baseEnd_3508682] using wordTrace_append hprefix tailTrace_3508682
  have hstable : (prefixWord ++ tailWord_3508682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508682).length < 2 ^ (prefixWord ++ tailWord_3508682).sum := by decide
  have hdescent : baseEnd_3508682 < baseStart_3508682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508692 : List Nat := [2, 4, 1, 2, 2, 1, 11]
def baseStart_3508692 : Nat := 118140960795 + 3508692 * 2 ^ 59
def prefixEnd_3508692 : Nat := 4983230072969 + 3 ^ 40 * 3508692 * 2
def baseEnd_3508692 : Nat := 22242536599818413087825

theorem tailTrace_3508692 : CollatzResearch.WordTrace tailWord_3508692 prefixEnd_3508692 22242536599818413087825 := by
  unfold tailWord_3508692
  simp only [CollatzResearch.WordTrace]
  refine ⟨63986255302307797865512165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85315007069743730487349553 63986255302307797865512165)
  ·
    refine ⟨11997422869182712099783531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63986255302307797865512165 11997422869182712099783531)
    ·
      refine ⟨17996134303774068149675297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11997422869182712099783531 17996134303774068149675297)
      ·
        refine ⟨13497100727830551112256473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17996134303774068149675297 13497100727830551112256473)
        ·
          refine ⟨10122825545872913334192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13497100727830551112256473 10122825545872913334192355)
          ·
            refine ⟨15184238318809370001288533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122825545872913334192355 15184238318809370001288533)
            ·
              refine ⟨22242536599818413087825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15184238318809370001288533 22242536599818413087825)
              ·
                rfl

theorem cell23_3508692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 11].length) (baseStart_3508692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508692 prefixEnd_3508692 := by exact prefixLift 3508692
  have htrace : WordTrace (prefixWord ++ tailWord_3508692) baseStart_3508692 baseEnd_3508692 := by
    simpa [prefixWord, tailWord_3508692, baseEnd_3508692] using wordTrace_append hprefix tailTrace_3508692
  have hstable : (prefixWord ++ tailWord_3508692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508692).length < 2 ^ (prefixWord ++ tailWord_3508692).sum := by decide
  have hdescent : baseEnd_3508692 < baseStart_3508692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508703 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 3, 2, 2]
def baseStart_3508703 : Nat := 118140960795 + 3508703 * 2 ^ 59
def prefixEnd_3508703 : Nat := 4983230072969 + 3 ^ 40 * 3508703 * 2
def baseEnd_3508703 : Nat := 1801651112872490917076275

theorem tailTrace_3508703 : CollatzResearch.WordTrace tailWord_3508703 prefixEnd_3508703 1801651112872490917076275 := by
  unfold tailWord_3508703
  simp only [CollatzResearch.WordTrace]
  refine ⟨127972911807575744609674763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85315274538383829739783175 127972911807575744609674763)
  ·
    refine ⟨191959367711363616914512145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127972911807575744609674763 191959367711363616914512145)
    ·
      refine ⟨143969525783522712685884109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191959367711363616914512145 143969525783522712685884109)
      ·
        refine ⟨53988572168821017257206541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143969525783522712685884109 53988572168821017257206541)
        ·
          refine ⟨20245714563307881471452453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53988572168821017257206541 20245714563307881471452453)
          ·
            refine ⟨3796071480620227775897335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20245714563307881471452453 3796071480620227775897335)
            ·
              refine ⟨5694107220930341663846003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796071480620227775897335 5694107220930341663846003)
              ·
                refine ⟨8541160831395512495769005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694107220930341663846003 8541160831395512495769005)
                ·
                  refine ⟨3202935311773317185913377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8541160831395512495769005 3202935311773317185913377)
                  ·
                    refine ⟨2402201483829987889435033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3202935311773317185913377 2402201483829987889435033)
                    ·
                      refine ⟨1801651112872490917076275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402201483829987889435033 1801651112872490917076275)
                      ·
                        rfl

theorem cell23_3508703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_3508703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508703 prefixEnd_3508703 := by exact prefixLift 3508703
  have htrace : WordTrace (prefixWord ++ tailWord_3508703) baseStart_3508703 baseEnd_3508703 := by
    simpa [prefixWord, tailWord_3508703, baseEnd_3508703] using wordTrace_append hprefix tailTrace_3508703
  have hstable : (prefixWord ++ tailWord_3508703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508703).length < 2 ^ (prefixWord ++ tailWord_3508703).sum := by decide
  have hdescent : baseEnd_3508703 < baseStart_3508703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508709 : List Nat := [1, 3, 1, 5, 2, 1, 2, 8]
def baseStart_3508709 : Nat := 118140960795 + 3508709 * 2 ^ 59
def prefixEnd_3508709 : Nat := 4983230072969 + 3 ^ 40 * 3508709 * 2
def baseEnd_3508709 : Nat := 66727933102089551614861

theorem tailTrace_3508709 : CollatzResearch.WordTrace tailWord_3508709 prefixEnd_3508709 66727933102089551614861 := by
  unfold tailWord_3508709
  simp only [CollatzResearch.WordTrace]
  refine ⟨127973130645554007634393181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85315420430369338422928787 127973130645554007634393181)
  ·
    refine ⟨47989923992082752862897443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127973130645554007634393181 47989923992082752862897443)
    ·
      refine ⟨71984885988124129294346165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47989923992082752862897443 71984885988124129294346165)
      ·
        refine ⟨6748583061386637121344953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71984885988124129294346165 6748583061386637121344953)
        ·
          refine ⟨5061437296039977841008715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6748583061386637121344953 5061437296039977841008715)
          ·
            refine ⟨7592155944059966761513073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061437296039977841008715 7592155944059966761513073)
            ·
              refine ⟨5694116958044975071134805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592155944059966761513073 5694116958044975071134805)
              ·
                refine ⟨66727933102089551614861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5694116958044975071134805 66727933102089551614861)
                ·
                  rfl

theorem cell23_3508709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 8].length) (baseStart_3508709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508709 prefixEnd_3508709 := by exact prefixLift 3508709
  have htrace : WordTrace (prefixWord ++ tailWord_3508709) baseStart_3508709 baseEnd_3508709 := by
    simpa [prefixWord, tailWord_3508709, baseEnd_3508709] using wordTrace_append hprefix tailTrace_3508709
  have hstable : (prefixWord ++ tailWord_3508709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508709).length < 2 ^ (prefixWord ++ tailWord_3508709).sum := by decide
  have hdescent : baseEnd_3508709 < baseStart_3508709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508762 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3508762 : Nat := 118140960795 + 3508762 * 2 ^ 59
def prefixEnd_3508762 : Nat := 4983230072969 + 3 ^ 40 * 3508762 * 2
def baseEnd_3508762 : Nat := 1801681408231106186238503

theorem tailTrace_3508762 : CollatzResearch.WordTrace tailWord_3508762 prefixEnd_3508762 1801681408231106186238503 := by
  unfold tailWord_3508762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31993765928590499421518135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85316709142907998457381693 31993765928590499421518135)
  ·
    refine ⟨47990648892885749132277203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31993765928590499421518135 47990648892885749132277203)
    ·
      refine ⟨71985973339328623698415805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47990648892885749132277203 71985973339328623698415805)
      ·
        refine ⟨26994740002248233886905927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71985973339328623698415805 26994740002248233886905927)
        ·
          refine ⟨40492110003372350830358891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26994740002248233886905927 40492110003372350830358891)
          ·
            refine ⟨60738165005058526245538337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40492110003372350830358891 60738165005058526245538337)
            ·
              refine ⟨45553623753793894684153753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60738165005058526245538337 45553623753793894684153753)
              ·
                refine ⟨34165217815345421013115315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45553623753793894684153753 34165217815345421013115315)
                ·
                  refine ⟨51247826723018131519672973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34165217815345421013115315 51247826723018131519672973)
                  ·
                    refine ⟨19217935021131799319877365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51247826723018131519672973 19217935021131799319877365)
                    ·
                      refine ⟨1801681408231106186238503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19217935021131799319877365 1801681408231106186238503)
                      ·
                        rfl

theorem cell23_3508762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3508762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508762 prefixEnd_3508762 := by exact prefixLift 3508762
  have htrace : WordTrace (prefixWord ++ tailWord_3508762) baseStart_3508762 baseEnd_3508762 := by
    simpa [prefixWord, tailWord_3508762, baseEnd_3508762] using wordTrace_append hprefix tailTrace_3508762
  have hstable : (prefixWord ++ tailWord_3508762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508762).length < 2 ^ (prefixWord ++ tailWord_3508762).sum := by decide
  have hdescent : baseEnd_3508762 < baseStart_3508762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508804 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3508804 : Nat := 118140960795 + 3508804 * 2 ^ 59
def prefixEnd_3508804 : Nat := 4983230072969 + 3 ^ 40 * 3508804 * 2
def baseEnd_3508804 : Nat := 1801702974418595021913311

theorem tailTrace_3508804 : CollatzResearch.WordTrace tailWord_3508804 prefixEnd_3508804 1801702974418595021913311 := by
  unfold tailWord_3508804
  simp only [CollatzResearch.WordTrace]
  refine ⟨63988297790104919429550733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85317730386806559239400977 63988297790104919429550733)
  ·
    refine ⟨23995611671289344786081525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63988297790104919429550733 23995611671289344786081525)
    ·
      refine ⟨2249588594183376073695143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23995611671289344786081525 2249588594183376073695143)
      ·
        refine ⟨3374382891275064110542715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249588594183376073695143 3374382891275064110542715)
        ·
          refine ⟨5061574336912596165814073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374382891275064110542715 5061574336912596165814073)
          ·
            refine ⟨3796180752684447124360555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061574336912596165814073 3796180752684447124360555)
            ·
              refine ⟨5694271129026670686540833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796180752684447124360555 5694271129026670686540833)
              ·
                refine ⟨4270703346770003014905625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694271129026670686540833 4270703346770003014905625)
                ·
                  refine ⟨3203027510077502261179219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270703346770003014905625 3203027510077502261179219)
                  ·
                    refine ⟨4804541265116253391768829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203027510077502261179219 4804541265116253391768829)
                    ·
                      refine ⟨1801702974418595021913311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4804541265116253391768829 1801702974418595021913311)
                      ·
                        rfl

theorem cell23_3508804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3508804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508804 prefixEnd_3508804 := by exact prefixLift 3508804
  have htrace : WordTrace (prefixWord ++ tailWord_3508804) baseStart_3508804 baseEnd_3508804 := by
    simpa [prefixWord, tailWord_3508804, baseEnd_3508804] using wordTrace_append hprefix tailTrace_3508804
  have hstable : (prefixWord ++ tailWord_3508804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508804).length < 2 ^ (prefixWord ++ tailWord_3508804).sum := by decide
  have hdescent : baseEnd_3508804 < baseStart_3508804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508810 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_3508810 : Nat := 118140960795 + 3508810 * 2 ^ 59
def prefixEnd_3508810 : Nat := 4983230072969 + 3 ^ 40 * 3508810 * 2
def baseEnd_3508810 : Nat := 1801706055302521998438283

theorem tailTrace_3508810 : CollatzResearch.WordTrace tailWord_3508810 prefixEnd_3508810 1801706055302521998438283 := by
  unfold tailWord_3508810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31994203604547025470954971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85317876278792067922546589 31994203604547025470954971)
  ·
    refine ⟨47991305406820538206432457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31994203604547025470954971 47991305406820538206432457)
    ·
      refine ⟨35993479055115403654824343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47991305406820538206432457 35993479055115403654824343)
      ·
        refine ⟨53990218582673105482236515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35993479055115403654824343 53990218582673105482236515)
        ·
          refine ⟨80985327874009658223354773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53990218582673105482236515 80985327874009658223354773)
          ·
            refine ⟨3796187244094202729219755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80985327874009658223354773 3796187244094202729219755)
            ·
              refine ⟨5694280866141304093829633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796187244094202729219755 5694280866141304093829633)
              ·
                refine ⟨4270710649605978070372225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694280866141304093829633 4270710649605978070372225)
                ·
                  refine ⟨3203032987204483552779169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270710649605978070372225 3203032987204483552779169)
                  ·
                    refine ⟨2402274740403362664584377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3203032987204483552779169 2402274740403362664584377)
                    ·
                      refine ⟨1801706055302521998438283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402274740403362664584377 1801706055302521998438283)
                      ·
                        rfl

theorem cell23_3508810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_3508810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508810 prefixEnd_3508810 := by exact prefixLift 3508810
  have htrace : WordTrace (prefixWord ++ tailWord_3508810) baseStart_3508810 baseEnd_3508810 := by
    simpa [prefixWord, tailWord_3508810, baseEnd_3508810] using wordTrace_append hprefix tailTrace_3508810
  have hstable : (prefixWord ++ tailWord_3508810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508810).length < 2 ^ (prefixWord ++ tailWord_3508810).sum := by decide
  have hdescent : baseEnd_3508810 < baseStart_3508810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508850 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_3508850 : Nat := 118140960795 + 3508850 * 2 ^ 59
def prefixEnd_3508850 : Nat := 4983230072969 + 3 ^ 40 * 3508850 * 2
def baseEnd_3508850 : Nat := 200191843836522426882011

theorem tailTrace_3508850 : CollatzResearch.WordTrace tailWord_3508850 prefixEnd_3508850 200191843836522426882011 := by
  unfold tailWord_3508850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31994568334510797178819001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85318848892028792476850669 31994568334510797178819001)
  ·
    refine ⟨23995926250883097884114251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31994568334510797178819001 23995926250883097884114251)
    ·
      refine ⟨35993889376324646826171377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23995926250883097884114251 35993889376324646826171377)
      ·
        refine ⟨26995417032243485119628533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35993889376324646826171377 26995417032243485119628533)
        ·
          refine ⟨2530820346772826729965175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26995417032243485119628533 2530820346772826729965175)
          ·
            refine ⟨3796230520159240094947763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530820346772826729965175 3796230520159240094947763)
            ·
              refine ⟨5694345780238860142421645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796230520159240094947763 5694345780238860142421645)
              ·
                refine ⟨2135379667589572553408117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5694345780238860142421645 2135379667589572553408117)
                ·
                  refine ⟨200191843836522426882011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2135379667589572553408117 200191843836522426882011)
                  ·
                    rfl

theorem cell23_3508850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_3508850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508850 prefixEnd_3508850 := by exact prefixLift 3508850
  have htrace : WordTrace (prefixWord ++ tailWord_3508850) baseStart_3508850 baseEnd_3508850 := by
    simpa [prefixWord, tailWord_3508850, baseEnd_3508850] using wordTrace_append hprefix tailTrace_3508850
  have hstable : (prefixWord ++ tailWord_3508850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508850).length < 2 ^ (prefixWord ++ tailWord_3508850).sum := by decide
  have hdescent : baseEnd_3508850 < baseStart_3508850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508889 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 6]
def baseStart_3508889 : Nat := 118140960795 + 3508889 * 2 ^ 59
def prefixEnd_3508889 : Nat := 4983230072969 + 3 ^ 40 * 3508889 * 2
def baseEnd_3508889 : Nat := 200194068919358576594491

theorem tailTrace_3508889 : CollatzResearch.WordTrace tailWord_3508889 prefixEnd_3508889 200194068919358576594491 := by
  unfold tailWord_3508889
  simp only [CollatzResearch.WordTrace]
  refine ⟨127979695784901898375945721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85319797189934598917297147 127979695784901898375945721)
  ·
    refine ⟨95984771838676423781959291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127979695784901898375945721 95984771838676423781959291)
    ·
      refine ⟨143977157758014635672938937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95984771838676423781959291 143977157758014635672938937)
      ·
        refine ⟨107982868318510976754704203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143977157758014635672938937 107982868318510976754704203)
        ·
          refine ⟨161974302477766465132056305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107982868318510976754704203 161974302477766465132056305)
          ·
            refine ⟨121480726858324848849042229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161974302477766465132056305 121480726858324848849042229)
            ·
              refine ⟨11388818142967954579597709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121480726858324848849042229 11388818142967954579597709)
              ·
                refine ⟨4270806803612982967349141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11388818142967954579597709 4270806803612982967349141)
                ·
                  refine ⟨200194068919358576594491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4270806803612982967349141 200194068919358576594491)
                  ·
                    rfl

theorem cell23_3508889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_3508889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508889 prefixEnd_3508889 := by exact prefixLift 3508889
  have htrace : WordTrace (prefixWord ++ tailWord_3508889) baseStart_3508889 baseEnd_3508889 := by
    simpa [prefixWord, tailWord_3508889, baseEnd_3508889] using wordTrace_append hprefix tailTrace_3508889
  have hstable : (prefixWord ++ tailWord_3508889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508889).length < 2 ^ (prefixWord ++ tailWord_3508889).sum := by decide
  have hdescent : baseEnd_3508889 < baseStart_3508889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3508973 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3508973 : Nat := 118140960795 + 3508973 * 2 ^ 59
def prefixEnd_3508973 : Nat := 4983230072969 + 3 ^ 40 * 3508973 * 2
def baseEnd_3508973 : Nat := 1801789752649204860700033

theorem tailTrace_3508973 : CollatzResearch.WordTrace tailWord_3508973 prefixEnd_3508973 1801789752649204860700033 := by
  unfold tailWord_3508973
  simp only [CollatzResearch.WordTrace]
  refine ⟨127982759516597580722003573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85321839677731720481335715 127982759516597580722003573)
  ·
    refine ⟨11998383704681023192687835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127982759516597580722003573 11998383704681023192687835)
    ·
      refine ⟨17997575557021534789031753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998383704681023192687835 17997575557021534789031753)
      ·
        refine ⟨13498181667766151091773815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17997575557021534789031753 13498181667766151091773815)
        ·
          refine ⟨20247272501649226637660723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498181667766151091773815 20247272501649226637660723)
          ·
            refine ⟨30370908752473839956491085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20247272501649226637660723 30370908752473839956491085)
            ·
              refine ⟨11389090782177689983684157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30370908752473839956491085 11389090782177689983684157)
              ·
                refine ⟨4270909043316633743881559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11389090782177689983684157 4270909043316633743881559)
                ·
                  refine ⟨6406363564974950615822339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270909043316633743881559 6406363564974950615822339)
                  ·
                    refine ⟨9609545347462425923733509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6406363564974950615822339 9609545347462425923733509)
                    ·
                      refine ⟨1801789752649204860700033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9609545347462425923733509 1801789752649204860700033)
                      ·
                        rfl

theorem cell23_3508973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3508973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3508973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3508973 prefixEnd_3508973 := by exact prefixLift 3508973
  have htrace : WordTrace (prefixWord ++ tailWord_3508973) baseStart_3508973 baseEnd_3508973 := by
    simpa [prefixWord, tailWord_3508973, baseEnd_3508973] using wordTrace_append hprefix tailTrace_3508973
  have hstable : (prefixWord ++ tailWord_3508973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3508973).length < 2 ^ (prefixWord ++ tailWord_3508973).sum := by decide
  have hdescent : baseEnd_3508973 < baseStart_3508973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3508973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509000 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 2, 4]
def baseStart_3509000 : Nat := 118140960795 + 3509000 * 2 ^ 59
def prefixEnd_3509000 : Nat := 4983230072969 + 3 ^ 40 * 3509000 * 2
def baseEnd_3509000 : Nat := 600601205542292085020803

theorem tailTrace_3509000 : CollatzResearch.WordTrace tailWord_3509000 prefixEnd_3509000 600601205542292085020803 := by
  unfold tailWord_3509000
  simp only [CollatzResearch.WordTrace]
  refine ⟨63991872143749882166618227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85322496191666509555490969 63991872143749882166618227)
  ·
    refine ⟨95987808215624823249927341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63991872143749882166618227 95987808215624823249927341)
    ·
      refine ⟨35995428080859308718722753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95987808215624823249927341 35995428080859308718722753)
      ·
        refine ⟨26996571060644481539042065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35995428080859308718722753 26996571060644481539042065)
        ·
          refine ⟨20247428295483361154281549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26996571060644481539042065 20247428295483361154281549)
          ·
            refine ⟨7592785610806260432855581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20247428295483361154281549 7592785610806260432855581)
            ·
              refine ⟨2847294604052347662320843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7592785610806260432855581 2847294604052347662320843)
              ·
                refine ⟨4270941906078521493481265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847294604052347662320843 4270941906078521493481265)
                ·
                  refine ⟨3203206429558891120110949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270941906078521493481265 3203206429558891120110949)
                  ·
                    refine ⟨600601205542292085020803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203206429558891120110949 600601205542292085020803)
                    ·
                      rfl

theorem cell23_3509000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_3509000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509000 prefixEnd_3509000 := by exact prefixLift 3509000
  have htrace : WordTrace (prefixWord ++ tailWord_3509000) baseStart_3509000 baseEnd_3509000 := by
    simpa [prefixWord, tailWord_3509000, baseEnd_3509000] using wordTrace_append hprefix tailTrace_3509000
  have hstable : (prefixWord ++ tailWord_3509000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509000).length < 2 ^ (prefixWord ++ tailWord_3509000).sum := by decide
  have hdescent : baseEnd_3509000 < baseStart_3509000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509009 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3509009 : Nat := 118140960795 + 3509009 * 2 ^ 59
def prefixEnd_3509009 : Nat := 4983230072969 + 3 ^ 40 * 3509009 * 2
def baseEnd_3509009 : Nat := 600602745984255573283289

theorem tailTrace_3509009 : CollatzResearch.WordTrace tailWord_3509009 prefixEnd_3509009 600602745984255573283289 := by
  unfold tailWord_3509009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127984072544467158870314081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85322715029644772580209387 127984072544467158870314081)
  ·
    refine ⟨95988054408350369152735561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127984072544467158870314081 95988054408350369152735561)
    ·
      refine ⟨71991040806262776864551671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95988054408350369152735561 71991040806262776864551671)
      ·
        refine ⟨107986561209394165296827507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71991040806262776864551671 107986561209394165296827507)
        ·
          refine ⟨161979841814091247945241261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107986561209394165296827507 161979841814091247945241261)
          ·
            refine ⟨60742440680284217979465473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161979841814091247945241261 60742440680284217979465473)
            ·
              refine ⟨45556830510213163484599105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60742440680284217979465473 45556830510213163484599105)
              ·
                refine ⟨34167622882659872613449329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45556830510213163484599105 34167622882659872613449329)
                ·
                  refine ⟨25625717161994904460086997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34167622882659872613449329 25625717161994904460086997)
                  ·
                    refine ⟨600602745984255573283289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25625717161994904460086997 600602745984255573283289)
                    ·
                      rfl

theorem cell23_3509009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3509009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509009 prefixEnd_3509009 := by exact prefixLift 3509009
  have htrace : WordTrace (prefixWord ++ tailWord_3509009) baseStart_3509009 baseEnd_3509009 := by
    simpa [prefixWord, tailWord_3509009, baseEnd_3509009] using wordTrace_append hprefix tailTrace_3509009
  have hstable : (prefixWord ++ tailWord_3509009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509009).length < 2 ^ (prefixWord ++ tailWord_3509009).sum := by decide
  have hdescent : baseEnd_3509009 < baseStart_3509009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509023 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 3]
def baseStart_3509023 : Nat := 118140960795 + 3509023 * 2 ^ 59
def prefixEnd_3509023 : Nat := 4983230072969 + 3 ^ 40 * 3509023 * 2
def baseEnd_3509023 : Nat := 1801815426681929665074803

theorem tailTrace_3509023 : CollatzResearch.WordTrace tailWord_3509023 prefixEnd_3509023 1801815426681929665074803 := by
  unfold tailWord_3509023
  simp only [CollatzResearch.WordTrace]
  refine ⟨127984583166416439261323723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85323055444277626174215815 127984583166416439261323723)
  ·
    refine ⟨191976874749624658891985585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127984583166416439261323723 191976874749624658891985585)
    ·
      refine ⟨143982656062218494168989189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191976874749624658891985585 143982656062218494168989189)
      ·
        refine ⟨26996748011665967656685473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143982656062218494168989189 26996748011665967656685473)
        ·
          refine ⟨20247561008749475742514105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26996748011665967656685473 20247561008749475742514105)
          ·
            refine ⟨15185670756562106806885579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20247561008749475742514105 15185670756562106806885579)
            ·
              refine ⟨22778506134843160210328369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15185670756562106806885579 22778506134843160210328369)
              ·
                refine ⟨17083879601132370157746277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22778506134843160210328369 17083879601132370157746277)
                ·
                  refine ⟨3203227425212319404577427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17083879601132370157746277 3203227425212319404577427)
                  ·
                    refine ⟨4804841137818479106866141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203227425212319404577427 4804841137818479106866141)
                    ·
                      refine ⟨1801815426681929665074803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4804841137818479106866141 1801815426681929665074803)
                      ·
                        rfl

theorem cell23_3509023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_3509023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509023 prefixEnd_3509023 := by exact prefixLift 3509023
  have htrace : WordTrace (prefixWord ++ tailWord_3509023) baseStart_3509023 baseEnd_3509023 := by
    simpa [prefixWord, tailWord_3509023, baseEnd_3509023] using wordTrace_append hprefix tailTrace_3509023
  have hstable : (prefixWord ++ tailWord_3509023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509023).length < 2 ^ (prefixWord ++ tailWord_3509023).sum := by decide
  have hdescent : baseEnd_3509023 < baseStart_3509023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509024 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3509024 : Nat := 118140960795 + 3509024 * 2 ^ 59
def prefixEnd_3509024 : Nat := 4983230072969 + 3 ^ 40 * 3509024 * 2
def baseEnd_3509024 : Nat := 1801815940162584161162299

theorem tailTrace_3509024 : CollatzResearch.WordTrace tailWord_3509024 prefixEnd_3509024 1801815940162584161162299 := by
  unfold tailWord_3509024
  simp only [CollatzResearch.WordTrace]
  refine ⟨63992309819706408216055063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85323079759608544288073417 63992309819706408216055063)
  ·
    refine ⟨95988464729559612324082595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63992309819706408216055063 95988464729559612324082595)
    ·
      refine ⟨143982697094339418486123893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95988464729559612324082595 143982697094339418486123893)
      ·
        refine ⟨13498377852594320483074115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143982697094339418486123893 13498377852594320483074115)
        ·
          refine ⟨20247566778891480724611173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498377852594320483074115 20247566778891480724611173)
          ·
            refine ⟨3796418771042152635864595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20247566778891480724611173 3796418771042152635864595)
            ·
              refine ⟨5694628156563228953796893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796418771042152635864595 5694628156563228953796893)
              ·
                refine ⟨2135485558711210857673835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5694628156563228953796893 2135485558711210857673835)
                ·
                  refine ⟨3203228338066816286510753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135485558711210857673835 3203228338066816286510753)
                  ·
                    refine ⟨2402421253550112214883065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3203228338066816286510753 2402421253550112214883065)
                    ·
                      refine ⟨1801815940162584161162299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402421253550112214883065 1801815940162584161162299)
                      ·
                        rfl

theorem cell23_3509024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3509024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509024 prefixEnd_3509024 := by exact prefixLift 3509024
  have htrace : WordTrace (prefixWord ++ tailWord_3509024) baseStart_3509024 baseEnd_3509024 := by
    simpa [prefixWord, tailWord_3509024, baseEnd_3509024] using wordTrace_append hprefix tailTrace_3509024
  have hstable : (prefixWord ++ tailWord_3509024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509024).length < 2 ^ (prefixWord ++ tailWord_3509024).sum := by decide
  have hdescent : baseEnd_3509024 < baseStart_3509024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509063 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_3509063 : Nat := 118140960795 + 3509063 * 2 ^ 59
def prefixEnd_3509063 : Nat := 4983230072969 + 3 ^ 40 * 3509063 * 2
def baseEnd_3509063 : Nat := 1801835965908109508574619

theorem tailTrace_3509063 : CollatzResearch.WordTrace tailWord_3509063 prefixEnd_3509063 1801835965908109508574619 := by
  unfold tailWord_3509063
  simp only [CollatzResearch.WordTrace]
  refine ⟨127986042086271526092779843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85324028057514350728519895 127986042086271526092779843)
  ·
    refine ⟨191979063129407289139169765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127986042086271526092779843 191979063129407289139169765)
    ·
      refine ⟨35996074336763866713594331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191979063129407289139169765 35996074336763866713594331)
      ·
        refine ⟨53994111505145800070391497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35996074336763866713594331 53994111505145800070391497)
        ·
          refine ⟨40495583628859350052793623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53994111505145800070391497 40495583628859350052793623)
          ·
            refine ⟨60743375443289025079190435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40495583628859350052793623 60743375443289025079190435)
            ·
              refine ⟨91115063164933537618785653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60743375443289025079190435 91115063164933537618785653)
              ·
                refine ⟨8542037171712519151761155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91115063164933537618785653 8542037171712519151761155)
                ·
                  refine ⟨12813055757568778727641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542037171712519151761155 12813055757568778727641733)
                  ·
                    refine ⟨2402447954544146011432825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12813055757568778727641733 2402447954544146011432825)
                    ·
                      refine ⟨1801835965908109508574619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402447954544146011432825 1801835965908109508574619)
                      ·
                        rfl

theorem cell23_3509063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_3509063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509063 prefixEnd_3509063 := by exact prefixLift 3509063
  have htrace : WordTrace (prefixWord ++ tailWord_3509063) baseStart_3509063 baseEnd_3509063 := by
    simpa [prefixWord, tailWord_3509063, baseEnd_3509063] using wordTrace_append hprefix tailTrace_3509063
  have hstable : (prefixWord ++ tailWord_3509063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509063).length < 2 ^ (prefixWord ++ tailWord_3509063).sum := by decide
  have hdescent : baseEnd_3509063 < baseStart_3509063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509066 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_3509066 : Nat := 118140960795 + 3509066 * 2 ^ 59
def prefixEnd_3509066 : Nat := 4983230072969 + 3 ^ 40 * 3509066 * 2
def baseEnd_3509066 : Nat := 1801837506350072996837105

theorem tailTrace_3509066 : CollatzResearch.WordTrace tailWord_3509066 prefixEnd_3509066 1801837506350072996837105 := by
  unfold tailWord_3509066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31996537876315164401284763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85324101003507105070092701 31996537876315164401284763)
  ·
    refine ⟨47994806814472746601927145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31996537876315164401284763 47994806814472746601927145)
    ·
      refine ⟨35996105110854559951445359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47994806814472746601927145 35996105110854559951445359)
      ·
        refine ⟨53994157666281839927168039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35996105110854559951445359 53994157666281839927168039)
        ·
          refine ⟨80991236499422759890752059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53994157666281839927168039 80991236499422759890752059)
          ·
            refine ⟨121486854749134139836128089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80991236499422759890752059 121486854749134139836128089)
            ·
              refine ⟨91115141061850604877096067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121486854749134139836128089 91115141061850604877096067)
              ·
                refine ⟨136672711592775907315644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91115141061850604877096067 136672711592775907315644101)
                ·
                  refine ⟨25626133423645482621683269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136672711592775907315644101 25626133423645482621683269)
                  ·
                    refine ⟨4804900016933527991565613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25626133423645482621683269 4804900016933527991565613)
                    ·
                      refine ⟨1801837506350072996837105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4804900016933527991565613 1801837506350072996837105)
                      ·
                        rfl

theorem cell23_3509066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_3509066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509066 prefixEnd_3509066 := by exact prefixLift 3509066
  have htrace : WordTrace (prefixWord ++ tailWord_3509066) baseStart_3509066 baseEnd_3509066 := by
    simpa [prefixWord, tailWord_3509066, baseEnd_3509066] using wordTrace_append hprefix tailTrace_3509066
  have hstable : (prefixWord ++ tailWord_3509066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509066).length < 2 ^ (prefixWord ++ tailWord_3509066).sum := by decide
  have hdescent : baseEnd_3509066 < baseStart_3509066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509084 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3509084 : Nat := 118140960795 + 3509084 * 2 ^ 59
def prefixEnd_3509084 : Nat := 4983230072969 + 3 ^ 40 * 3509084 * 2
def baseEnd_3509084 : Nat := 1801846749001853926412023

theorem tailTrace_3509084 : CollatzResearch.WordTrace tailWord_3509084 prefixEnd_3509084 1801846749001853926412023 := by
  unfold tailWord_3509084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63993404009597723339647153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85324538679463631119529537 63993404009597723339647153)
  ·
    refine ⟨47995053007198292504735365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63993404009597723339647153 47995053007198292504735365)
    ·
      refine ⟨8999072438849679844637881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47995053007198292504735365 8999072438849679844637881)
      ·
        refine ⟨6749304329137259883478411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8999072438849679844637881 6749304329137259883478411)
        ·
          refine ⟨10123956493705889825217617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749304329137259883478411 10123956493705889825217617)
          ·
            refine ⟨7592967370279417368913213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123956493705889825217617 7592967370279417368913213)
            ·
              refine ⟨2847362763854781513342455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7592967370279417368913213 2847362763854781513342455)
              ·
                refine ⟨4271044145782172270013683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847362763854781513342455 4271044145782172270013683)
                ·
                  refine ⟨6406566218673258405020525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271044145782172270013683 6406566218673258405020525)
                  ·
                    refine ⟨2402462332002471901882697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6406566218673258405020525 2402462332002471901882697)
                    ·
                      refine ⟨1801846749001853926412023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402462332002471901882697 1801846749001853926412023)
                      ·
                        rfl

theorem cell23_3509084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3509084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509084 prefixEnd_3509084 := by exact prefixLift 3509084
  have htrace : WordTrace (prefixWord ++ tailWord_3509084) baseStart_3509084 baseEnd_3509084 := by
    simpa [prefixWord, tailWord_3509084, baseEnd_3509084] using wordTrace_append hprefix tailTrace_3509084
  have hstable : (prefixWord ++ tailWord_3509084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509084).length < 2 ^ (prefixWord ++ tailWord_3509084).sum := by decide
  have hdescent : baseEnd_3509084 < baseStart_3509084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509110 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3509110 : Nat := 118140960795 + 3509110 * 2 ^ 59
def prefixEnd_3509110 : Nat := 4983230072969 + 3 ^ 40 * 3509110 * 2
def baseEnd_3509110 : Nat := 1801860099498870824686903

theorem tailTrace_3509110 : CollatzResearch.WordTrace tailWord_3509110 prefixEnd_3509110 1801860099498870824686903 := by
  unfold tailWord_3509110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999234769818828319983799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85325170878067502079827189 7999234769818828319983799)
  ·
    refine ⟨11998852154728242479975699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7999234769818828319983799 11998852154728242479975699)
    ·
      refine ⟨17998278232092363719963549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998852154728242479975699 17998278232092363719963549)
      ·
        refine ⟨6749354337034636394986331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17998278232092363719963549 6749354337034636394986331)
        ·
          refine ⟨10124031505551954592479497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749354337034636394986331 10124031505551954592479497)
          ·
            refine ⟨7593023629163965944359623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124031505551954592479497 7593023629163965944359623)
            ·
              refine ⟨11389535443745948916539435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593023629163965944359623 11389535443745948916539435)
              ·
                refine ⟨17084303165618923374809153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389535443745948916539435 17084303165618923374809153)
                ·
                  refine ⟨12813227374214192531106865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17084303165618923374809153 12813227374214192531106865)
                  ·
                    refine ⟨9609920530660644398330149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12813227374214192531106865 9609920530660644398330149)
                    ·
                      refine ⟨1801860099498870824686903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9609920530660644398330149 1801860099498870824686903)
                      ·
                        rfl

theorem cell23_3509110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3509110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509110 prefixEnd_3509110 := by exact prefixLift 3509110
  have htrace : WordTrace (prefixWord ++ tailWord_3509110) baseStart_3509110 baseEnd_3509110 := by
    simpa [prefixWord, tailWord_3509110, baseEnd_3509110] using wordTrace_append hprefix tailTrace_3509110
  have hstable : (prefixWord ++ tailWord_3509110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509110).length < 2 ^ (prefixWord ++ tailWord_3509110).sum := by decide
  have hdescent : baseEnd_3509110 < baseStart_3509110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509113 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3509113 : Nat := 118140960795 + 3509113 * 2 ^ 59
def prefixEnd_3509113 : Nat := 4983230072969 + 3 ^ 40 * 3509113 * 2
def baseEnd_3509113 : Nat := 1801861639940834312949389

theorem tailTrace_3509113 : CollatzResearch.WordTrace tailWord_3509113 prefixEnd_3509113 1801861639940834312949389 := by
  unfold tailWord_3509113
  simp only [CollatzResearch.WordTrace]
  refine ⟨127987865736090384632099993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85325243824060256421399995 127987865736090384632099993)
  ·
    refine ⟨95990899302067788474074995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127987865736090384632099993 95990899302067788474074995)
    ·
      refine ⟨143986348953101682711112493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95990899302067788474074995 143986348953101682711112493)
      ·
        refine ⟨53994880857413131016667185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143986348953101682711112493 53994880857413131016667185)
        ·
          refine ⟨40496160643059848262500389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53994880857413131016667185 40496160643059848262500389)
          ·
            refine ⟨7593030120573721549218823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40496160643059848262500389 7593030120573721549218823)
            ·
              refine ⟨11389545180860582323828235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593030120573721549218823 11389545180860582323828235)
              ·
                refine ⟨17084317771290873485742353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11389545180860582323828235 17084317771290873485742353)
                ·
                  refine ⟨12813238328468155114306765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17084317771290873485742353 12813238328468155114306765)
                  ·
                    refine ⟨4804964373175558167865037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12813238328468155114306765 4804964373175558167865037)
                    ·
                      refine ⟨1801861639940834312949389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4804964373175558167865037 1801861639940834312949389)
                      ·
                        rfl

theorem cell23_3509113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3509113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509113 prefixEnd_3509113 := by exact prefixLift 3509113
  have htrace : WordTrace (prefixWord ++ tailWord_3509113) baseStart_3509113 baseEnd_3509113 := by
    simpa [prefixWord, tailWord_3509113, baseEnd_3509113] using wordTrace_append hprefix tailTrace_3509113
  have hstable : (prefixWord ++ tailWord_3509113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509113).length < 2 ^ (prefixWord ++ tailWord_3509113).sum := by decide
  have hdescent : baseEnd_3509113 < baseStart_3509113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509116 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3509116 : Nat := 118140960795 + 3509116 * 2 ^ 59
def prefixEnd_3509116 : Nat := 4983230072969 + 3 ^ 40 * 3509116 * 2
def baseEnd_3509116 : Nat := 600621060127599267070625

theorem tailTrace_3509116 : CollatzResearch.WordTrace tailWord_3509116 prefixEnd_3509116 600621060127599267070625 := by
  unfold tailWord_3509116
  simp only [CollatzResearch.WordTrace]
  refine ⟨63993987577539758072229601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85325316770053010762972801 63993987577539758072229601)
  ·
    refine ⟨47995490683154818554172201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63993987577539758072229601 47995490683154818554172201)
    ·
      refine ⟨35996618012366113915629151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47995490683154818554172201 35996618012366113915629151)
      ·
        refine ⟨53994927018549170873443727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35996618012366113915629151 53994927018549170873443727)
        ·
          refine ⟨80992390527823756310165591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53994927018549170873443727 80992390527823756310165591)
          ·
            refine ⟨121488585791735634465248387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80992390527823756310165591 121488585791735634465248387)
            ·
              refine ⟨182232878687603451697872581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121488585791735634465248387 182232878687603451697872581)
              ·
                refine ⟨34168664753925647193351109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182232878687603451697872581 34168664753925647193351109)
                ·
                  refine ⟨6406624641361058848753333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34168664753925647193351109 6406624641361058848753333)
                  ·
                    refine ⟨600621060127599267070625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6406624641361058848753333 600621060127599267070625)
                    ·
                      rfl

theorem cell23_3509116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3509116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509116 prefixEnd_3509116 := by exact prefixLift 3509116
  have htrace : WordTrace (prefixWord ++ tailWord_3509116) baseStart_3509116 baseEnd_3509116 := by
    simpa [prefixWord, tailWord_3509116, baseEnd_3509116] using wordTrace_append hprefix tailTrace_3509116
  have hstable : (prefixWord ++ tailWord_3509116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509116).length < 2 ^ (prefixWord ++ tailWord_3509116).sum := by decide
  have hdescent : baseEnd_3509116 < baseStart_3509116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509123 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 5, 2]
def baseStart_3509123 : Nat := 118140960795 + 3509123 * 2 ^ 59
def prefixEnd_3509123 : Nat := 4983230072969 + 3 ^ 40 * 3509123 * 2
def baseEnd_3509123 : Nat := 1801866774747379273824343

theorem tailTrace_3509123 : CollatzResearch.WordTrace tailWord_3509123 prefixEnd_3509123 1801866774747379273824343 := by
  unfold tailWord_3509123
  simp only [CollatzResearch.WordTrace]
  refine ⟨127988230466054156339964023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85325486977369437559976015 127988230466054156339964023)
  ·
    refine ⟨191982345699081234509946035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127988230466054156339964023 191982345699081234509946035)
    ·
      refine ⟨287973518548621851764919053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191982345699081234509946035 287973518548621851764919053)
      ·
        refine ⟨107990069455733194411844645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287973518548621851764919053 107990069455733194411844645)
        ·
          refine ⟨20248138022949973952220871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107990069455733194411844645 20248138022949973952220871)
          ·
            refine ⟨30372207034424960928331307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20248138022949973952220871 30372207034424960928331307)
            ·
              refine ⟨45558310551637441392496961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30372207034424960928331307 45558310551637441392496961)
              ·
                refine ⟨34168732913728081044372721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45558310551637441392496961 34168732913728081044372721)
                ·
                  refine ⟨25626549685296060783279541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34168732913728081044372721 25626549685296060783279541)
                  ·
                    refine ⟨2402489032996505698432457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25626549685296060783279541 2402489032996505698432457)
                    ·
                      refine ⟨1801866774747379273824343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402489032996505698432457 1801866774747379273824343)
                      ·
                        rfl

theorem cell23_3509123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_3509123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509123 prefixEnd_3509123 := by exact prefixLift 3509123
  have htrace : WordTrace (prefixWord ++ tailWord_3509123) baseStart_3509123 baseEnd_3509123 := by
    simpa [prefixWord, tailWord_3509123, baseEnd_3509123] using wordTrace_append hprefix tailTrace_3509123
  have hstable : (prefixWord ++ tailWord_3509123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509123).length < 2 ^ (prefixWord ++ tailWord_3509123).sum := by decide
  have hdescent : baseEnd_3509123 < baseStart_3509123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509173 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3509173 : Nat := 118140960795 + 3509173 * 2 ^ 59
def prefixEnd_3509173 : Nat := 4983230072969 + 3 ^ 40 * 3509173 * 2
def baseEnd_3509173 : Nat := 1801892448780104078199113

theorem tailTrace_3509173 : CollatzResearch.WordTrace tailWord_3509173 prefixEnd_3509173 1801892448780104078199113 := by
  unfold tailWord_3509173
  simp only [CollatzResearch.WordTrace]
  refine ⟨127990054115873014879284173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85326702743915343252856115 127990054115873014879284173)
  ·
    refine ⟨47996270293452380579731565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127990054115873014879284173 47996270293452380579731565)
    ·
      refine ⟨17998601360044642717399337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47996270293452380579731565 17998601360044642717399337)
      ·
        refine ⟨13498951020033482038049503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17998601360044642717399337 13498951020033482038049503)
        ·
          refine ⟨20248426530050223057074255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498951020033482038049503 20248426530050223057074255)
          ·
            refine ⟨30372639795075334585611383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20248426530050223057074255 30372639795075334585611383)
            ·
              refine ⟨45558959692613001878417075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30372639795075334585611383 45558959692613001878417075)
              ·
                refine ⟨68338439538919502817625613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45558959692613001878417075 68338439538919502817625613)
                ·
                  refine ⟨25626914827094813556609605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68338439538919502817625613 25626914827094813556609605)
                  ·
                    refine ⟨4805046530080277541864301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25626914827094813556609605 4805046530080277541864301)
                    ·
                      refine ⟨1801892448780104078199113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4805046530080277541864301 1801892448780104078199113)
                      ·
                        rfl

theorem cell23_3509173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3509173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509173 prefixEnd_3509173 := by exact prefixLift 3509173
  have htrace : WordTrace (prefixWord ++ tailWord_3509173) baseStart_3509173 baseEnd_3509173 := by
    simpa [prefixWord, tailWord_3509173, baseEnd_3509173] using wordTrace_append hprefix tailTrace_3509173
  have hstable : (prefixWord ++ tailWord_3509173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509173).length < 2 ^ (prefixWord ++ tailWord_3509173).sum := by decide
  have hdescent : baseEnd_3509173 < baseStart_3509173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509216 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3509216 : Nat := 118140960795 + 3509216 * 2 ^ 59
def prefixEnd_3509216 : Nat := 4983230072969 + 3 ^ 40 * 3509216 * 2
def baseEnd_3509216 : Nat := 1801914528448247409961415

theorem tailTrace_3509216 : CollatzResearch.WordTrace tailWord_3509216 prefixEnd_3509216 1801914528448247409961415 := by
  unfold tailWord_3509216
  simp only [CollatzResearch.WordTrace]
  refine ⟨63995811227358616611549751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85327748303144822148733001 63995811227358616611549751)
  ·
    refine ⟨95993716841037924917324627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63995811227358616611549751 95993716841037924917324627)
    ·
      refine ⟨143990575261556887375986941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95993716841037924917324627 143990575261556887375986941)
      ·
        refine ⟨53996465723083832765995103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143990575261556887375986941 53996465723083832765995103)
        ·
          refine ⟨80994698584625749148992655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53996465723083832765995103 80994698584625749148992655)
          ·
            refine ⟨121492047876938623723488983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80994698584625749148992655 121492047876938623723488983)
            ·
              refine ⟨182238071815407935585233475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121492047876938623723488983 182238071815407935585233475)
              ·
                refine ⟨273357107723111903377850213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182238071815407935585233475 273357107723111903377850213)
                ·
                  refine ⟨51254457698083481883346915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273357107723111903377850213 51254457698083481883346915)
                  ·
                    refine ⟨76881686547125222825020373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51254457698083481883346915 76881686547125222825020373)
                    ·
                      refine ⟨1801914528448247409961415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76881686547125222825020373 1801914528448247409961415)
                      ·
                        rfl

theorem cell23_3509216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3509216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509216 prefixEnd_3509216 := by exact prefixLift 3509216
  have htrace : WordTrace (prefixWord ++ tailWord_3509216) baseStart_3509216 baseEnd_3509216 := by
    simpa [prefixWord, tailWord_3509216, baseEnd_3509216] using wordTrace_append hprefix tailTrace_3509216
  have hstable : (prefixWord ++ tailWord_3509216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509216).length < 2 ^ (prefixWord ++ tailWord_3509216).sum := by decide
  have hdescent : baseEnd_3509216 < baseStart_3509216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509220 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_3509220 : Nat := 118140960795 + 3509220 * 2 ^ 59
def prefixEnd_3509220 : Nat := 4983230072969 + 3 ^ 40 * 3509220 * 2
def baseEnd_3509220 : Nat := 1801916582370865394311397

theorem tailTrace_3509220 : CollatzResearch.WordTrace tailWord_3509220 prefixEnd_3509220 1801916582370865394311397 := by
  unfold tailWord_3509220
  simp only [CollatzResearch.WordTrace]
  refine ⟨63995884173351370953122557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85327845564468494604163409 63995884173351370953122557)
  ·
    refine ⟨23998456565006764107420959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63995884173351370953122557 23998456565006764107420959)
    ·
      refine ⟨35997684847510146161131439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23998456565006764107420959 35997684847510146161131439)
      ·
        refine ⟨53996527271265219241697159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35997684847510146161131439 53996527271265219241697159)
        ·
          refine ⟨80994790906897828862545739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53996527271265219241697159 80994790906897828862545739)
          ·
            refine ⟨121492186360346743293818609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80994790906897828862545739 121492186360346743293818609)
            ·
              refine ⟨91119139770260057470363957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121492186360346743293818609 91119139770260057470363957)
              ·
                refine ⟨8542419353461880387846621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91119139770260057470363957 8542419353461880387846621)
                ·
                  refine ⟨3203407257548205145442483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8542419353461880387846621 3203407257548205145442483)
                  ·
                    refine ⟨4805110886322307718163725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203407257548205145442483 4805110886322307718163725)
                    ·
                      refine ⟨1801916582370865394311397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4805110886322307718163725 1801916582370865394311397)
                      ·
                        rfl

theorem cell23_3509220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_3509220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509220 prefixEnd_3509220 := by exact prefixLift 3509220
  have htrace : WordTrace (prefixWord ++ tailWord_3509220) baseStart_3509220 baseEnd_3509220 := by
    simpa [prefixWord, tailWord_3509220, baseEnd_3509220] using wordTrace_append hprefix tailTrace_3509220
  have hstable : (prefixWord ++ tailWord_3509220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509220).length < 2 ^ (prefixWord ++ tailWord_3509220).sum := by decide
  have hdescent : baseEnd_3509220 < baseStart_3509220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509253 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_3509253 : Nat := 118140960795 + 3509253 * 2 ^ 59
def prefixEnd_3509253 : Nat := 4983230072969 + 3 ^ 40 * 3509253 * 2
def baseEnd_3509253 : Nat := 600644509077487921732915

theorem tailTrace_3509253 : CollatzResearch.WordTrace tailWord_3509253 prefixEnd_3509253 600644509077487921732915 := by
  unfold tailWord_3509253
  simp only [CollatzResearch.WordTrace]
  refine ⟨127992971955583188542196413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85328647970388792361464275 127992971955583188542196413)
  ·
    refine ⟨47997364483343695703323655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127992971955583188542196413 47997364483343695703323655)
    ·
      refine ⟨71996046725015543554985483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47997364483343695703323655 71996046725015543554985483)
      ·
        refine ⟨107994070087523315332478225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71996046725015543554985483 107994070087523315332478225)
        ·
          refine ⟨80995552565642486499358669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107994070087523315332478225 80995552565642486499358669)
          ·
            refine ⟨30373332212115932437259501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80995552565642486499358669 30373332212115932437259501)
            ·
              refine ⟨11389999579543474663972313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30373332212115932437259501 11389999579543474663972313)
              ·
                refine ⟨8542499684657605997979235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11389999579543474663972313 8542499684657605997979235)
                ·
                  refine ⟨12813749526986408996968853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542499684657605997979235 12813749526986408996968853)
                  ·
                    refine ⟨600644509077487921732915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12813749526986408996968853 600644509077487921732915)
                    ·
                      rfl

theorem cell23_3509253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_3509253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509253 prefixEnd_3509253 := by exact prefixLift 3509253
  have htrace : WordTrace (prefixWord ++ tailWord_3509253) baseStart_3509253 baseEnd_3509253 := by
    simpa [prefixWord, tailWord_3509253, baseEnd_3509253] using wordTrace_append hprefix tailTrace_3509253
  have hstable : (prefixWord ++ tailWord_3509253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509253).length < 2 ^ (prefixWord ++ tailWord_3509253).sum := by decide
  have hdescent : baseEnd_3509253 < baseStart_3509253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509271 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3509271 : Nat := 118140960795 + 3509271 * 2 ^ 59
def prefixEnd_3509271 : Nat := 4983230072969 + 3 ^ 40 * 3509271 * 2
def baseEnd_3509271 : Nat := 1801942769884244694773663

theorem tailTrace_3509271 : CollatzResearch.WordTrace tailWord_3509271 prefixEnd_3509271 1801942769884244694773663 := by
  unfold tailWord_3509271
  simp only [CollatzResearch.WordTrace]
  refine ⟨127993628469517977616351667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85329085646345318410901111 127993628469517977616351667)
  ·
    refine ⟨191990442704276966424527501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127993628469517977616351667 191990442704276966424527501)
    ·
      refine ⟨71996416014103862409197813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191990442704276966424527501 71996416014103862409197813)
      ·
        refine ⟨6749664001322237100862295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71996416014103862409197813 6749664001322237100862295)
        ·
          refine ⟨10124496001983355651293443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749664001322237100862295 10124496001983355651293443)
          ·
            refine ⟨15186744002975033476940165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124496001983355651293443 15186744002975033476940165)
            ·
              refine ⟨2847514500557818776926281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15186744002975033476940165 2847514500557818776926281)
              ·
                refine ⟨2135635875418364082694711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847514500557818776926281 2135635875418364082694711)
                ·
                  refine ⟨3203453813127546124042067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135635875418364082694711 3203453813127546124042067)
                  ·
                    refine ⟨4805180719691319186063101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203453813127546124042067 4805180719691319186063101)
                    ·
                      refine ⟨1801942769884244694773663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4805180719691319186063101 1801942769884244694773663)
                      ·
                        rfl

theorem cell23_3509271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3509271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509271 prefixEnd_3509271 := by exact prefixLift 3509271
  have htrace : WordTrace (prefixWord ++ tailWord_3509271) baseStart_3509271 baseEnd_3509271 := by
    simpa [prefixWord, tailWord_3509271, baseEnd_3509271] using wordTrace_append hprefix tailTrace_3509271
  have hstable : (prefixWord ++ tailWord_3509271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509271).length < 2 ^ (prefixWord ++ tailWord_3509271).sum := by decide
  have hdescent : baseEnd_3509271 < baseStart_3509271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509283 : List Nat := [1, 1, 1, 4, 3, 2, 3, 8]
def baseStart_3509283 : Nat := 118140960795 + 3509283 * 2 ^ 59
def prefixEnd_3509283 : Nat := 4983230072969 + 3 ^ 40 * 3509283 * 2
def baseEnd_3509283 : Nat := 66738849320448098067541

theorem tailTrace_3509283 : CollatzResearch.WordTrace tailWord_3509283 prefixEnd_3509283 66738849320448098067541 := by
  unfold tailWord_3509283
  simp only [CollatzResearch.WordTrace]
  refine ⟨127994066145474503665788503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85329377430316335777192335 127994066145474503665788503)
  ·
    refine ⟨191991099218211755498682755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127994066145474503665788503 191991099218211755498682755)
    ·
      refine ⟨287986648827317633248024133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191991099218211755498682755 287986648827317633248024133)
      ·
        refine ⟨53997496655122056234004525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287986648827317633248024133 53997496655122056234004525)
        ·
          refine ⟨20249061245670771087751697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53997496655122056234004525 20249061245670771087751697)
          ·
            refine ⟨15186795934253078315813773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20249061245670771087751697 15186795934253078315813773)
            ·
              refine ⟨5695048475344904368430165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15186795934253078315813773 5695048475344904368430165)
              ·
                refine ⟨66738849320448098067541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5695048475344904368430165 66738849320448098067541)
                ·
                  rfl

theorem cell23_3509283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 8].length) (baseStart_3509283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509283 prefixEnd_3509283 := by exact prefixLift 3509283
  have htrace : WordTrace (prefixWord ++ tailWord_3509283) baseStart_3509283 baseEnd_3509283 := by
    simpa [prefixWord, tailWord_3509283, baseEnd_3509283] using wordTrace_append hprefix tailTrace_3509283
  have hstable : (prefixWord ++ tailWord_3509283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509283).length < 2 ^ (prefixWord ++ tailWord_3509283).sum := by decide
  have hdescent : baseEnd_3509283 < baseStart_3509283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509287 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3509287 : Nat := 118140960795 + 3509287 * 2 ^ 59
def prefixEnd_3509287 : Nat := 4983230072969 + 3 ^ 40 * 3509287 * 2
def baseEnd_3509287 : Nat := 600650328524905544057863

theorem tailTrace_3509287 : CollatzResearch.WordTrace tailWord_3509287 prefixEnd_3509287 600650328524905544057863 := by
  unfold tailWord_3509287
  simp only [CollatzResearch.WordTrace]
  refine ⟨127994212037460012348934115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85329474691640008232622743 127994212037460012348934115)
  ·
    refine ⟨191991318056190018523401173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127994212037460012348934115 191991318056190018523401173)
    ·
      refine ⟨4499796516941953559142215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 191991318056190018523401173 4499796516941953559142215)
      ·
        refine ⟨6749694775412930338713323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499796516941953559142215 6749694775412930338713323)
        ·
          refine ⟨10124542163119395508069985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749694775412930338713323 10124542163119395508069985)
          ·
            refine ⟨7593406622339546631052489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124542163119395508069985 7593406622339546631052489)
            ·
              refine ⟨5695054966754659973289367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593406622339546631052489 5695054966754659973289367)
              ·
                refine ⟨8542582450131989959934051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695054966754659973289367 8542582450131989959934051)
                ·
                  refine ⟨12813873675197984939901077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542582450131989959934051 12813873675197984939901077)
                  ·
                    refine ⟨600650328524905544057863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12813873675197984939901077 600650328524905544057863)
                    ·
                      rfl

theorem cell23_3509287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3509287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509287 prefixEnd_3509287 := by exact prefixLift 3509287
  have htrace : WordTrace (prefixWord ++ tailWord_3509287) baseStart_3509287 baseEnd_3509287 := by
    simpa [prefixWord, tailWord_3509287, baseEnd_3509287] using wordTrace_append hprefix tailTrace_3509287
  have hstable : (prefixWord ++ tailWord_3509287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509287).length < 2 ^ (prefixWord ++ tailWord_3509287).sum := by decide
  have hdescent : baseEnd_3509287 < baseStart_3509287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509294 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3509294 : Nat := 118140960795 + 3509294 * 2 ^ 59
def prefixEnd_3509294 : Nat := 4983230072969 + 3 ^ 40 * 3509294 * 2
def baseEnd_3509294 : Nat := 1801954579939298104786057

theorem tailTrace_3509294 : CollatzResearch.WordTrace tailWord_3509294 prefixEnd_3509294 1801954579939298104786057 := by
  unfold tailWord_3509294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999308418554331568054867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85329644898956435029625957 15999308418554331568054867)
  ·
    refine ⟨23998962627831497352082301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15999308418554331568054867 23998962627831497352082301)
    ·
      refine ⟨8999610985436811507030863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23998962627831497352082301 8999610985436811507030863)
      ·
        refine ⟨13499416478155217260546295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999610985436811507030863 13499416478155217260546295)
        ·
          refine ⟨20249124717232825890819443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13499416478155217260546295 20249124717232825890819443)
          ·
            refine ⟨30373687075849238836229165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20249124717232825890819443 30373687075849238836229165)
            ·
              refine ⟨11390132653443464563585937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30373687075849238836229165 11390132653443464563585937)
              ·
                refine ⟨8542599490082598422689453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11390132653443464563585937 8542599490082598422689453)
                ·
                  refine ⟨3203474808780974408508545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8542599490082598422689453 3203474808780974408508545)
                  ·
                    refine ⟨2402606106585730806381409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3203474808780974408508545 2402606106585730806381409)
                    ·
                      refine ⟨1801954579939298104786057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402606106585730806381409 1801954579939298104786057)
                      ·
                        rfl

theorem cell23_3509294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3509294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509294 prefixEnd_3509294 := by exact prefixLift 3509294
  have htrace : WordTrace (prefixWord ++ tailWord_3509294) baseStart_3509294 baseEnd_3509294 := by
    simpa [prefixWord, tailWord_3509294, baseEnd_3509294] using wordTrace_append hprefix tailTrace_3509294
  have hstable : (prefixWord ++ tailWord_3509294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509294).length < 2 ^ (prefixWord ++ tailWord_3509294).sum := by decide
  have hdescent : baseEnd_3509294 < baseStart_3509294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509341 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3509341 : Nat := 118140960795 + 3509341 * 2 ^ 59
def prefixEnd_3509341 : Nat := 4983230072969 + 3 ^ 40 * 3509341 * 2
def baseEnd_3509341 : Nat := 1801978713530059420898341

theorem tailTrace_3509341 : CollatzResearch.WordTrace tailWord_3509341 prefixEnd_3509341 1801978713530059420898341 := by
  unfold tailWord_3509341
  simp only [CollatzResearch.WordTrace]
  refine ⟨127996181579264379571399877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85330787719509586380933251 127996181579264379571399877)
  ·
    refine ⟨23999284046112071169637477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127996181579264379571399877 23999284046112071169637477)
    ·
      refine ⟨4499865758646013344307027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23999284046112071169637477 4499865758646013344307027)
      ·
        refine ⟨6749798637969020016460541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499865758646013344307027 6749798637969020016460541)
        ·
          refine ⟨2531174489238382506172703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6749798637969020016460541 2531174489238382506172703)
          ·
            refine ⟨3796761733857573759259055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531174489238382506172703 3796761733857573759259055)
            ·
              refine ⟨5695142600786360638888583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796761733857573759259055 5695142600786360638888583)
              ·
                refine ⟨8542713901179540958332875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695142600786360638888583 8542713901179540958332875)
                ·
                  refine ⟨12814070851769311437499313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8542713901179540958332875 12814070851769311437499313)
                  ·
                    refine ⟨9610553138826983578124485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12814070851769311437499313 9610553138826983578124485)
                    ·
                      refine ⟨1801978713530059420898341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9610553138826983578124485 1801978713530059420898341)
                      ·
                        rfl

theorem cell23_3509341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3509341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509341 prefixEnd_3509341 := by exact prefixLift 3509341
  have htrace : WordTrace (prefixWord ++ tailWord_3509341) baseStart_3509341 baseEnd_3509341 := by
    simpa [prefixWord, tailWord_3509341, baseEnd_3509341] using wordTrace_append hprefix tailTrace_3509341
  have hstable : (prefixWord ++ tailWord_3509341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509341).length < 2 ^ (prefixWord ++ tailWord_3509341).sum := by decide
  have hdescent : baseEnd_3509341 < baseStart_3509341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509343 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 2, 6]
def baseStart_3509343 : Nat := 118140960795 + 3509343 * 2 ^ 59
def prefixEnd_3509343 : Nat := 4983230072969 + 3 ^ 40 * 3509343 * 2
def baseEnd_3509343 : Nat := 600659913497122804357777

theorem tailTrace_3509343 : CollatzResearch.WordTrace tailWord_3509343 prefixEnd_3509343 600659913497122804357777 := by
  unfold tailWord_3509343
  simp only [CollatzResearch.WordTrace]
  refine ⟨127996254525257133912972683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85330836350171422608648455 127996254525257133912972683)
  ·
    refine ⟨191994381787885700869459025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127996254525257133912972683 191994381787885700869459025)
    ·
      refine ⟨143995786340914275652094269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191994381787885700869459025 143995786340914275652094269)
      ·
        refine ⟨53998419877842853369535351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143995786340914275652094269 53998419877842853369535351)
        ·
          refine ⟨80997629816764280054303027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53998419877842853369535351 80997629816764280054303027)
          ·
            refine ⟨121496444725146420081454541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80997629816764280054303027 121496444725146420081454541)
            ·
              refine ⟨45561166771929907530545453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121496444725146420081454541 45561166771929907530545453)
              ·
                refine ⟨17085437539473715323954545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45561166771929907530545453 17085437539473715323954545)
                ·
                  refine ⟨12814078154605286492965909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17085437539473715323954545 12814078154605286492965909)
                  ·
                    refine ⟨600659913497122804357777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12814078154605286492965909 600659913497122804357777)
                    ·
                      rfl

theorem cell23_3509343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_3509343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509343 prefixEnd_3509343 := by exact prefixLift 3509343
  have htrace : WordTrace (prefixWord ++ tailWord_3509343) baseStart_3509343 baseEnd_3509343 := by
    simpa [prefixWord, tailWord_3509343, baseEnd_3509343] using wordTrace_append hprefix tailTrace_3509343
  have hstable : (prefixWord ++ tailWord_3509343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509343).length < 2 ^ (prefixWord ++ tailWord_3509343).sum := by decide
  have hdescent : baseEnd_3509343 < baseStart_3509343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509344 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3]
def baseStart_3509344 : Nat := 118140960795 + 3509344 * 2 ^ 59
def prefixEnd_3509344 : Nat := 4983230072969 + 3 ^ 40 * 3509344 * 2
def baseEnd_3509344 : Nat := 1801980253972022909160827

theorem tailTrace_3509344 : CollatzResearch.WordTrace tailWord_3509344 prefixEnd_3509344 1801980253972022909160827 := by
  unfold tailWord_3509344
  simp only [CollatzResearch.WordTrace]
  refine ⟨63998145499126755541879543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85330860665502340722506057 63998145499126755541879543)
  ·
    refine ⟨95997218248690133312819315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63998145499126755541879543 95997218248690133312819315)
    ·
      refine ⟨143995827373035199969228973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95997218248690133312819315 143995827373035199969228973)
      ·
        refine ⟨53998435264888199988460865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143995827373035199969228973 53998435264888199988460865)
        ·
          refine ⟨40498826448666149991345649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53998435264888199988460865 40498826448666149991345649)
          ·
            refine ⟨30374119836499612493509237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40498826448666149991345649 30374119836499612493509237)
            ·
              refine ⟨2847573734671838671266491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30374119836499612493509237 2847573734671838671266491)
              ·
                refine ⟨4271360602007758006899737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847573734671838671266491 4271360602007758006899737)
                ·
                  refine ⟨3203520451505818505174803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4271360602007758006899737 3203520451505818505174803)
                  ·
                    refine ⟨4805280677258727757762205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203520451505818505174803 4805280677258727757762205)
                    ·
                      refine ⟨1801980253972022909160827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4805280677258727757762205 1801980253972022909160827)
                      ·
                        rfl

theorem cell23_3509344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_3509344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509344 prefixEnd_3509344 := by exact prefixLift 3509344
  have htrace : WordTrace (prefixWord ++ tailWord_3509344) baseStart_3509344 baseEnd_3509344 := by
    simpa [prefixWord, tailWord_3509344, baseEnd_3509344] using wordTrace_append hprefix tailTrace_3509344
  have hstable : (prefixWord ++ tailWord_3509344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509344).length < 2 ^ (prefixWord ++ tailWord_3509344).sum := by decide
  have hdescent : baseEnd_3509344 < baseStart_3509344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509354 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_3509354 : Nat := 118140960795 + 3509354 * 2 ^ 59
def prefixEnd_3509354 : Nat := 4983230072969 + 3 ^ 40 * 3509354 * 2
def baseEnd_3509354 : Nat := 1801985388778567870035781

theorem tailTrace_3509354 : CollatzResearch.WordTrace tailWord_3509354 prefixEnd_3509354 1801985388778567870035781 := by
  unfold tailWord_3509354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31999163932054320697905779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85331103818811521861082077 31999163932054320697905779)
  ·
    refine ⟨47998745898081481046858669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31999163932054320697905779 47998745898081481046858669)
    ·
      refine ⟨17999529711780555392572001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47998745898081481046858669 17999529711780555392572001)
      ·
        refine ⟨13499647283835416544429001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17999529711780555392572001 13499647283835416544429001)
        ·
          refine ⟨10124735462876562408321751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13499647283835416544429001 10124735462876562408321751)
          ·
            refine ⟨15187103194314843612482627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124735462876562408321751 15187103194314843612482627)
            ·
              refine ⟨22780654791472265418723941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15187103194314843612482627 22780654791472265418723941)
              ·
                refine ⟨4271372773401049766010739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22780654791472265418723941 4271372773401049766010739)
                ·
                  refine ⟨6407059160101574649016109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271372773401049766010739 6407059160101574649016109)
                  ·
                    refine ⟨2402647185038090493381041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6407059160101574649016109 2402647185038090493381041)
                    ·
                      refine ⟨1801985388778567870035781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402647185038090493381041 1801985388778567870035781)
                      ·
                        rfl

theorem cell23_3509354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_3509354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509354 prefixEnd_3509354 := by exact prefixLift 3509354
  have htrace : WordTrace (prefixWord ++ tailWord_3509354) baseStart_3509354 baseEnd_3509354 := by
    simpa [prefixWord, tailWord_3509354, baseEnd_3509354] using wordTrace_append hprefix tailTrace_3509354
  have hstable : (prefixWord ++ tailWord_3509354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509354).length < 2 ^ (prefixWord ++ tailWord_3509354).sum := by decide
  have hdescent : baseEnd_3509354 < baseStart_3509354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509367 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_3509367 : Nat := 118140960795 + 3509367 * 2 ^ 59
def prefixEnd_3509367 : Nat := 4983230072969 + 3 ^ 40 * 3509367 * 2
def baseEnd_3509367 : Nat := 1801992064027076319173221

theorem tailTrace_3509367 : CollatzResearch.WordTrace tailWord_3509367 prefixEnd_3509367 1801992064027076319173221 := by
  unfold tailWord_3509367
  simp only [CollatzResearch.WordTrace]
  refine ⟨127997129877170186011846355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85331419918113457341230903 127997129877170186011846355)
  ·
    refine ⟨191995694815755279017769533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127997129877170186011846355 191995694815755279017769533)
    ·
      refine ⟨71998385555908229631663575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191995694815755279017769533 71998385555908229631663575)
      ·
        refine ⟨107997578333862344447495363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71998385555908229631663575 107997578333862344447495363)
        ·
          refine ⟨161996367500793516671243045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107997578333862344447495363 161996367500793516671243045)
          ·
            refine ⟨30374318906398784375858071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161996367500793516671243045 30374318906398784375858071)
            ·
              refine ⟨45561478359598176563787107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30374318906398784375858071 45561478359598176563787107)
              ·
                refine ⟨68342217539397264845680661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45561478359598176563787107 68342217539397264845680661)
                ·
                  refine ⟨3203541447159246789641281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68342217539397264845680661 3203541447159246789641281)
                  ·
                    refine ⟨2402656085369435092230961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3203541447159246789641281 2402656085369435092230961)
                    ·
                      refine ⟨1801992064027076319173221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2402656085369435092230961 1801992064027076319173221)
                      ·
                        rfl

theorem cell23_3509367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_3509367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509367 prefixEnd_3509367 := by exact prefixLift 3509367
  have htrace : WordTrace (prefixWord ++ tailWord_3509367) baseStart_3509367 baseEnd_3509367 := by
    simpa [prefixWord, tailWord_3509367, baseEnd_3509367] using wordTrace_append hprefix tailTrace_3509367
  have hstable : (prefixWord ++ tailWord_3509367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509367).length < 2 ^ (prefixWord ++ tailWord_3509367).sum := by decide
  have hdescent : baseEnd_3509367 < baseStart_3509367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509383 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3509383 : Nat := 118140960795 + 3509383 * 2 ^ 59
def prefixEnd_3509383 : Nat := 4983230072969 + 3 ^ 40 * 3509383 * 2
def baseEnd_3509383 : Nat := 1802000279717548256573147

theorem tailTrace_3509383 : CollatzResearch.WordTrace tailWord_3509383 prefixEnd_3509383 1802000279717548256573147 := by
  unfold tailWord_3509383
  simp only [CollatzResearch.WordTrace]
  refine ⟨127997713445112220744428803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85331808963408147162952535 127997713445112220744428803)
  ·
    refine ⟨191996570167668331116643205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127997713445112220744428803 191996570167668331116643205)
    ·
      refine ⟨35999356906437812084370601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191996570167668331116643205 35999356906437812084370601)
      ·
        refine ⟨26999517679828359063277951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35999356906437812084370601 26999517679828359063277951)
        ·
          refine ⟨40499276519742538594916927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26999517679828359063277951 40499276519742538594916927)
          ·
            refine ⟨60748914779613807892375391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40499276519742538594916927 60748914779613807892375391)
            ·
              refine ⟨91123372169420711838563087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60748914779613807892375391 91123372169420711838563087)
              ·
                refine ⟨136685058254131067757844631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91123372169420711838563087 136685058254131067757844631)
                ·
                  refine ⟨205027587381196601636766947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136685058254131067757844631 205027587381196601636766947)
                  ·
                    refine ⟨307541381071794902455150421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205027587381196601636766947 307541381071794902455150421)
                    ·
                      refine ⟨1802000279717548256573147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 307541381071794902455150421 1802000279717548256573147)
                      ·
                        rfl

theorem cell23_3509383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3509383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509383 prefixEnd_3509383 := by exact prefixLift 3509383
  have htrace : WordTrace (prefixWord ++ tailWord_3509383) baseStart_3509383 baseEnd_3509383 := by
    simpa [prefixWord, tailWord_3509383, baseEnd_3509383] using wordTrace_append hprefix tailTrace_3509383
  have hstable : (prefixWord ++ tailWord_3509383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509383).length < 2 ^ (prefixWord ++ tailWord_3509383).sum := by decide
  have hdescent : baseEnd_3509383 < baseStart_3509383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509441 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 5]
def baseStart_3509441 : Nat := 118140960795 + 3509441 * 2 ^ 59
def prefixEnd_3509441 : Nat := 4983230072969 + 3 ^ 40 * 3509441 * 2
def baseEnd_3509441 : Nat := 200225562399501003294209

theorem tailTrace_3509441 : CollatzResearch.WordTrace tailWord_3509441 prefixEnd_3509441 200225562399501003294209 := by
  unfold tailWord_3509441
  simp only [CollatzResearch.WordTrace]
  refine ⟨127999828878902096650040177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85333219252601397766693451 127999828878902096650040177)
  ·
    refine ⟨95999871659176572487530133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127999828878902096650040177 95999871659176572487530133)
    ·
      refine ⟨4499993984023901835352975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95999871659176572487530133 4499993984023901835352975)
      ·
        refine ⟨6749990976035852753029463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499993984023901835352975 6749990976035852753029463)
        ·
          refine ⟨10124986464053779129544195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749990976035852753029463 10124986464053779129544195)
          ·
            refine ⟨15187479696080668694316293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124986464053779129544195 15187479696080668694316293)
            ·
              refine ⟨2847652443015125380184305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15187479696080668694316293 2847652443015125380184305)
              ·
                refine ⟨2135739332261344035138229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847652443015125380184305 2135739332261344035138229)
                ·
                  refine ⟨200225562399501003294209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2135739332261344035138229 200225562399501003294209)
                  ·
                    rfl

theorem cell23_3509441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 5].length) (baseStart_3509441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509441 prefixEnd_3509441 := by exact prefixLift 3509441
  have htrace : WordTrace (prefixWord ++ tailWord_3509441) baseStart_3509441 baseEnd_3509441 := by
    simpa [prefixWord, tailWord_3509441, baseEnd_3509441] using wordTrace_append hprefix tailTrace_3509441
  have hstable : (prefixWord ++ tailWord_3509441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509441).length < 2 ^ (prefixWord ++ tailWord_3509441).sum := by decide
  have hdescent : baseEnd_3509441 < baseStart_3509441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509480 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 8]
def baseStart_3509480 : Nat := 118140960795 + 3509480 * 2 ^ 59
def prefixEnd_3509480 : Nat := 4983230072969 + 3 ^ 40 * 3509480 * 2
def baseEnd_3509480 : Nat := 200227787482337153006689

theorem tailTrace_3509480 : CollatzResearch.WordTrace tailWord_3509480 prefixEnd_3509480 200227787482337153006689 := by
  unfold tailWord_3509480
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000625662880403155354947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85334167550507204207139929 64000625662880403155354947)
  ·
    refine ⟨96000938494320604733032421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64000625662880403155354947 96000938494320604733032421)
    ·
      refine ⟨18000175967685113387443579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96000938494320604733032421 18000175967685113387443579)
      ·
        refine ⟨27000263951527670081165369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18000175967685113387443579 27000263951527670081165369)
        ·
          refine ⟨20250197963645752560874027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27000263951527670081165369 20250197963645752560874027)
          ·
            refine ⟨30375296945468628841311041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20250197963645752560874027 30375296945468628841311041)
            ·
              refine ⟨22781472709101471630983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30375296945468628841311041 22781472709101471630983281)
              ·
                refine ⟨17086104531826103723237461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22781472709101471630983281 17086104531826103723237461)
                ·
                  refine ⟨200227787482337153006689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17086104531826103723237461 200227787482337153006689)
                  ·
                    rfl

theorem cell23_3509480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_3509480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509480 prefixEnd_3509480 := by exact prefixLift 3509480
  have htrace : WordTrace (prefixWord ++ tailWord_3509480) baseStart_3509480 baseEnd_3509480 := by
    simpa [prefixWord, tailWord_3509480, baseEnd_3509480] using wordTrace_append hprefix tailTrace_3509480
  have hstable : (prefixWord ++ tailWord_3509480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509480).length < 2 ^ (prefixWord ++ tailWord_3509480).sum := by decide
  have hdescent : baseEnd_3509480 < baseStart_3509480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509484 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_3509484 : Nat := 118140960795 + 3509484 * 2 ^ 59
def prefixEnd_3509484 : Nat := 4983230072969 + 3 ^ 40 * 3509484 * 2
def baseEnd_3509484 : Nat := 600684047087884120470061

theorem tailTrace_3509484 : CollatzResearch.WordTrace tailWord_3509484 prefixEnd_3509484 600684047087884120470061 := by
  unfold tailWord_3509484
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000698608873157496927753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85334264811830876662570337 64000698608873157496927753)
  ·
    refine ⟨48000523956654868122695815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64000698608873157496927753 48000523956654868122695815)
    ·
      refine ⟨72000785934982302184043723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48000523956654868122695815 72000785934982302184043723)
      ·
        refine ⟨108001178902473453276065585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72000785934982302184043723 108001178902473453276065585)
        ·
          refine ⟨81000884176855089957049189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108001178902473453276065585 81000884176855089957049189)
          ·
            refine ⟨15187665783160329366946723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81000884176855089957049189 15187665783160329366946723)
            ·
              refine ⟨22781498674740494050420085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15187665783160329366946723 22781498674740494050420085)
              ·
                refine ⟨2135765500756921317226883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22781498674740494050420085 2135765500756921317226883)
                ·
                  refine ⟨3203648251135381975840325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135765500756921317226883 3203648251135381975840325)
                  ·
                    refine ⟨600684047087884120470061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203648251135381975840325 600684047087884120470061)
                    ·
                      rfl

theorem cell23_3509484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_3509484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509484 prefixEnd_3509484 := by exact prefixLift 3509484
  have htrace : WordTrace (prefixWord ++ tailWord_3509484) baseStart_3509484 baseEnd_3509484 := by
    simpa [prefixWord, tailWord_3509484, baseEnd_3509484] using wordTrace_append hprefix tailTrace_3509484
  have hstable : (prefixWord ++ tailWord_3509484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509484).length < 2 ^ (prefixWord ++ tailWord_3509484).sum := by decide
  have hdescent : baseEnd_3509484 < baseStart_3509484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509544 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3509544 : Nat := 118140960795 + 3509544 * 2 ^ 59
def prefixEnd_3509544 : Nat := 4983230072969 + 3 ^ 40 * 3509544 * 2
def baseEnd_3509544 : Nat := 600694316700974042219969

theorem tailTrace_3509544 : CollatzResearch.WordTrace tailWord_3509544 prefixEnd_3509544 600694316700974042219969 := by
  unfold tailWord_3509544
  simp only [CollatzResearch.WordTrace]
  refine ⟨64001792798764472620519843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85335723731685963494026457 64001792798764472620519843)
  ·
    refine ⟨96002689198146708930779765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64001792798764472620519843 96002689198146708930779765)
    ·
      refine ⟨9000252112326253962260603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96002689198146708930779765 9000252112326253962260603)
      ·
        refine ⟨13500378168489380943390905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000252112326253962260603 13500378168489380943390905)
        ·
          refine ⟨10125283626367035707543179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13500378168489380943390905 10125283626367035707543179)
          ·
            refine ⟨15187925439550553561314769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10125283626367035707543179 15187925439550553561314769)
            ·
              refine ⟨11390944079662915170986077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15187925439550553561314769 11390944079662915170986077)
              ·
                refine ⟨4271604029873593189119779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11390944079662915170986077 4271604029873593189119779)
                ·
                  refine ⟨6407406044810389783679669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271604029873593189119779 6407406044810389783679669)
                  ·
                    refine ⟨600694316700974042219969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6407406044810389783679669 600694316700974042219969)
                    ·
                      rfl

theorem cell23_3509544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3509544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509544 prefixEnd_3509544 := by exact prefixLift 3509544
  have htrace : WordTrace (prefixWord ++ tailWord_3509544) baseStart_3509544 baseEnd_3509544 := by
    simpa [prefixWord, tailWord_3509544, baseEnd_3509544] using wordTrace_append hprefix tailTrace_3509544
  have hstable : (prefixWord ++ tailWord_3509544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509544).length < 2 ^ (prefixWord ++ tailWord_3509544).sum := by decide
  have hdescent : baseEnd_3509544 < baseStart_3509544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509567 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_3509567 : Nat := 118140960795 + 3509567 * 2 ^ 59
def prefixEnd_3509567 : Nat := 4983230072969 + 3 ^ 40 * 3509567 * 2
def baseEnd_3509567 : Nat := 1802094760157975536672301

theorem tailTrace_3509567 : CollatzResearch.WordTrace tailWord_3509567 prefixEnd_3509567 1802094760157975536672301 := by
  unfold tailWord_3509567
  simp only [CollatzResearch.WordTrace]
  refine ⟨128004424476445620169126955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85336282984297080112751303 128004424476445620169126955)
  ·
    refine ⟨192006636714668430253690433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128004424476445620169126955 192006636714668430253690433)
    ·
      refine ⟨144004977536001322690267825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192006636714668430253690433 144004977536001322690267825)
      ·
        refine ⟨108003733152000992017700869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144004977536001322690267825 108003733152000992017700869)
        ·
          refine ⟨20250699966000186003318913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108003733152000992017700869 20250699966000186003318913)
          ·
            refine ⟨15188024974500139502489185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20250699966000186003318913 15188024974500139502489185)
            ·
              refine ⟨11391018730875104626866889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15188024974500139502489185 11391018730875104626866889)
              ·
                refine ⟨8543264048156328470150167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11391018730875104626866889 8543264048156328470150167)
                ·
                  refine ⟨12814896072234492705225251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543264048156328470150167 12814896072234492705225251)
                  ·
                    refine ⟨19222344108351739057837877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12814896072234492705225251 19222344108351739057837877)
                    ·
                      refine ⟨1802094760157975536672301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19222344108351739057837877 1802094760157975536672301)
                      ·
                        rfl

theorem cell23_3509567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_3509567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509567 prefixEnd_3509567 := by exact prefixLift 3509567
  have htrace : WordTrace (prefixWord ++ tailWord_3509567) baseStart_3509567 baseEnd_3509567 := by
    simpa [prefixWord, tailWord_3509567, baseEnd_3509567] using wordTrace_append hprefix tailTrace_3509567
  have hstable : (prefixWord ++ tailWord_3509567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509567).length < 2 ^ (prefixWord ++ tailWord_3509567).sum := by decide
  have hdescent : baseEnd_3509567 < baseStart_3509567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509621 : List Nat := [1, 3, 4, 1, 4, 1, 1, 8]
def baseStart_3509621 : Nat := 118140960795 + 3509621 * 2 ^ 59
def prefixEnd_3509621 : Nat := 4983230072969 + 3 ^ 40 * 3509621 * 2
def baseEnd_3509621 : Nat := 66745277337530308348039

theorem tailTrace_3509621 : CollatzResearch.WordTrace tailWord_3509621 prefixEnd_3509621 66745277337530308348039 := by
  unfold tailWord_3509621
  simp only [CollatzResearch.WordTrace]
  refine ⟨128006394018249987391592717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85337596012166658261061811 128006394018249987391592717)
  ·
    refine ⟨48002397756843745271847269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128006394018249987391592717 48002397756843745271847269)
    ·
      refine ⟨9000449579408202238471363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48002397756843745271847269 9000449579408202238471363)
      ·
        refine ⟨13500674369112303357707045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000449579408202238471363 13500674369112303357707045)
        ·
          refine ⟨2531376444208556879570071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13500674369112303357707045 2531376444208556879570071)
          ·
            refine ⟨3797064666312835319355107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531376444208556879570071 3797064666312835319355107)
            ·
              refine ⟨5695596999469252979032661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797064666312835319355107 5695596999469252979032661)
              ·
                refine ⟨66745277337530308348039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5695596999469252979032661 66745277337530308348039)
                ·
                  rfl

theorem cell23_3509621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 8].length) (baseStart_3509621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509621 prefixEnd_3509621 := by exact prefixLift 3509621
  have htrace : WordTrace (prefixWord ++ tailWord_3509621) baseStart_3509621 baseEnd_3509621 := by
    simpa [prefixWord, tailWord_3509621, baseEnd_3509621] using wordTrace_append hprefix tailTrace_3509621
  have hstable : (prefixWord ++ tailWord_3509621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509621).length < 2 ^ (prefixWord ++ tailWord_3509621).sum := by decide
  have hdescent : baseEnd_3509621 < baseStart_3509621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509667 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3509667 : Nat := 118140960795 + 3509667 * 2 ^ 59
def prefixEnd_3509667 : Nat := 4983230072969 + 3 ^ 40 * 3509667 * 2
def baseEnd_3509667 : Nat := 1802146108223425145421841

theorem tailTrace_3509667 : CollatzResearch.WordTrace tailWord_3509667 prefixEnd_3509667 1802146108223425145421841 := by
  unfold tailWord_3509667
  simp only [CollatzResearch.WordTrace]
  refine ⟨128008071776083337247767255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85338714517388891498511503 128008071776083337247767255)
  ·
    refine ⟨192012107664125005871650883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128008071776083337247767255 192012107664125005871650883)
    ·
      refine ⟨288018161496187508807476325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192012107664125005871650883 288018161496187508807476325)
      ·
        refine ⟨54003405280535157901401811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288018161496187508807476325 54003405280535157901401811)
        ·
          refine ⟨81005107920802736852102717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54003405280535157901401811 81005107920802736852102717)
          ·
            refine ⟨30376915470301026319538519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81005107920802736852102717 30376915470301026319538519)
            ·
              refine ⟨45565373205451539479307779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30376915470301026319538519 45565373205451539479307779)
              ·
                refine ⟨68348059808177309218961669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45565373205451539479307779 68348059808177309218961669)
                ·
                  refine ⟨12815261214033245478555313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68348059808177309218961669 12815261214033245478555313)
                  ·
                    refine ⟨9611445910524934108916485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12815261214033245478555313 9611445910524934108916485)
                    ·
                      refine ⟨1802146108223425145421841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9611445910524934108916485 1802146108223425145421841)
                      ·
                        rfl

theorem cell23_3509667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3509667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509667 prefixEnd_3509667 := by exact prefixLift 3509667
  have htrace : WordTrace (prefixWord ++ tailWord_3509667) baseStart_3509667 baseEnd_3509667 := by
    simpa [prefixWord, tailWord_3509667, baseEnd_3509667] using wordTrace_append hprefix tailTrace_3509667
  have hstable : (prefixWord ++ tailWord_3509667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509667).length < 2 ^ (prefixWord ++ tailWord_3509667).sum := by decide
  have hdescent : baseEnd_3509667 < baseStart_3509667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509707 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 7]
def baseStart_3509707 : Nat := 118140960795 + 3509707 * 2 ^ 59
def prefixEnd_3509707 : Nat := 4983230072969 + 3 ^ 40 * 3509707 * 2
def baseEnd_3509707 : Nat := 600722215816534996307219

theorem tailTrace_3509707 : CollatzResearch.WordTrace tailWord_3509707 prefixEnd_3509707 600722215816534996307219 := by
  unfold tailWord_3509707
  simp only [CollatzResearch.WordTrace]
  refine ⟨128009530695938424079223375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85339687130625616052815583 128009530695938424079223375)
  ·
    refine ⟨192014296043907636118835063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128009530695938424079223375 192014296043907636118835063)
    ·
      refine ⟨288021444065861454178252595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192014296043907636118835063 288021444065861454178252595)
      ·
        refine ⟨432032166098792181267378893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288021444065861454178252595 432032166098792181267378893)
        ·
          refine ⟨162012062287047067975267085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432032166098792181267378893 162012062287047067975267085)
          ·
            refine ⟨60754523357642650490725157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162012062287047067975267085 60754523357642650490725157)
            ·
              refine ⟨11391473129557996967010967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60754523357642650490725157 11391473129557996967010967)
              ·
                refine ⟨17087209694336995450516451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391473129557996967010967 17087209694336995450516451)
                ·
                  refine ⟨25630814541505493175774677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17087209694336995450516451 25630814541505493175774677)
                  ·
                    refine ⟨600722215816534996307219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25630814541505493175774677 600722215816534996307219)
                    ·
                      rfl

theorem cell23_3509707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_3509707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509707 prefixEnd_3509707 := by exact prefixLift 3509707
  have htrace : WordTrace (prefixWord ++ tailWord_3509707) baseStart_3509707 baseEnd_3509707 := by
    simpa [prefixWord, tailWord_3509707, baseEnd_3509707] using wordTrace_append hprefix tailTrace_3509707
  have hstable : (prefixWord ++ tailWord_3509707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509707).length < 2 ^ (prefixWord ++ tailWord_3509707).sum := by decide
  have hdescent : baseEnd_3509707 < baseStart_3509707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509754 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_3509754 : Nat := 118140960795 + 3509754 * 2 ^ 59
def prefixEnd_3509754 : Nat := 4983230072969 + 3 ^ 40 * 3509754 * 2
def baseEnd_3509754 : Nat := 600730260346788768344647

theorem tailTrace_3509754 : CollatzResearch.WordTrace tailWord_3509754 prefixEnd_3509754 600730260346788768344647 := by
  unfold tailWord_3509754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32002811231692037776546079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85340829951178767404122877 32002811231692037776546079)
  ·
    refine ⟨48004216847538056664819119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32002811231692037776546079 48004216847538056664819119)
    ·
      refine ⟨72006325271307084997228679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48004216847538056664819119 72006325271307084997228679)
      ·
        refine ⟨108009487906960627495843019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72006325271307084997228679 108009487906960627495843019)
        ·
          refine ⟨162014231860440941243764529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108009487906960627495843019 162014231860440941243764529)
          ·
            refine ⟨121510673895330705932823397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162014231860440941243764529 121510673895330705932823397)
            ·
              refine ⟨22783251355374507362404387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121510673895330705932823397 22783251355374507362404387)
              ·
                refine ⟨34174877033061761043606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22783251355374507362404387 34174877033061761043606581)
                ·
                  refine ⟨3203894721849540097838117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34174877033061761043606581 3203894721849540097838117)
                  ·
                    refine ⟨600730260346788768344647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203894721849540097838117 600730260346788768344647)
                    ·
                      rfl

theorem cell23_3509754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_3509754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509754 prefixEnd_3509754 := by exact prefixLift 3509754
  have htrace : WordTrace (prefixWord ++ tailWord_3509754) baseStart_3509754 baseEnd_3509754 := by
    simpa [prefixWord, tailWord_3509754, baseEnd_3509754] using wordTrace_append hprefix tailTrace_3509754
  have hstable : (prefixWord ++ tailWord_3509754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509754).length < 2 ^ (prefixWord ++ tailWord_3509754).sum := by decide
  have hdescent : baseEnd_3509754 < baseStart_3509754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509781 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_3509781 : Nat := 118140960795 + 3509781 * 2 ^ 59
def prefixEnd_3509781 : Nat := 4983230072969 + 3 ^ 40 * 3509781 * 2
def baseEnd_3509781 : Nat := 1802204645018037699396317

theorem tailTrace_3509781 : CollatzResearch.WordTrace tailWord_3509781 prefixEnd_3509781 1802204645018037699396317 := by
  unfold tailWord_3509781
  simp only [CollatzResearch.WordTrace]
  refine ⟨128012229697670334717417197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85341486465113556478278131 128012229697670334717417197)
  ·
    refine ⟨48004586136626375519031449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128012229697670334717417197 48004586136626375519031449)
    ·
      refine ⟨36003439602469781639273587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48004586136626375519031449 36003439602469781639273587)
      ·
        refine ⟨54005159403704672458910381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36003439602469781639273587 54005159403704672458910381)
        ·
          refine ⟨20251934776389252172091393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54005159403704672458910381 20251934776389252172091393)
          ·
            refine ⟨15188951082291939129068545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20251934776389252172091393 15188951082291939129068545)
            ·
              refine ⟨11391713311718954346801409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15188951082291939129068545 11391713311718954346801409)
              ·
                refine ⟨8543784983789215760101057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11391713311718954346801409 8543784983789215760101057)
                ·
                  refine ⟨6407838737841911820075793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8543784983789215760101057 6407838737841911820075793)
                  ·
                    refine ⟨4805879053381433865056845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6407838737841911820075793 4805879053381433865056845)
                    ·
                      refine ⟨1802204645018037699396317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4805879053381433865056845 1802204645018037699396317)
                      ·
                        rfl

theorem cell23_3509781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_3509781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509781 prefixEnd_3509781 := by exact prefixLift 3509781
  have htrace : WordTrace (prefixWord ++ tailWord_3509781) baseStart_3509781 baseEnd_3509781 := by
    simpa [prefixWord, tailWord_3509781, baseEnd_3509781] using wordTrace_append hprefix tailTrace_3509781
  have hstable : (prefixWord ++ tailWord_3509781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509781).length < 2 ^ (prefixWord ++ tailWord_3509781).sum := by decide
  have hdescent : baseEnd_3509781 < baseStart_3509781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509788 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_3509788 : Nat := 118140960795 + 3509788 * 2 ^ 59
def prefixEnd_3509788 : Nat := 4983230072969 + 3 ^ 40 * 3509788 * 2
def baseEnd_3509788 : Nat := 600736079794206390669595

theorem tailTrace_3509788 : CollatzResearch.WordTrace tailWord_3509788 prefixEnd_3509788 600736079794206390669595 := by
  unfold tailWord_3509788
  simp only [CollatzResearch.WordTrace]
  refine ⟨64006242504322487456461009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85341656672429983275281345 64006242504322487456461009)
  ·
    refine ⟨48004681878241865592345757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64006242504322487456461009 48004681878241865592345757)
    ·
      refine ⟨18001755704340699597129659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48004681878241865592345757 18001755704340699597129659)
      ·
        refine ⟨27002633556511049395694489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18001755704340699597129659 27002633556511049395694489)
        ·
          refine ⟨20251975167383287046770867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27002633556511049395694489 20251975167383287046770867)
          ·
            refine ⟨30377962751074930570156301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20251975167383287046770867 30377962751074930570156301)
            ·
              refine ⟨11391736031653098963808613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30377962751074930570156301 11391736031653098963808613)
              ·
                refine ⟨2135950505934956055714115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11391736031653098963808613 2135950505934956055714115)
                ·
                  refine ⟨3203925758902434083571173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135950505934956055714115 3203925758902434083571173)
                  ·
                    refine ⟨600736079794206390669595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203925758902434083571173 600736079794206390669595)
                    ·
                      rfl

theorem cell23_3509788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_3509788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509788 prefixEnd_3509788 := by exact prefixLift 3509788
  have htrace : WordTrace (prefixWord ++ tailWord_3509788) baseStart_3509788 baseEnd_3509788 := by
    simpa [prefixWord, tailWord_3509788, baseEnd_3509788] using wordTrace_append hprefix tailTrace_3509788
  have hstable : (prefixWord ++ tailWord_3509788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509788).length < 2 ^ (prefixWord ++ tailWord_3509788).sum := by decide
  have hdescent : baseEnd_3509788 < baseStart_3509788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509811 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 3]
def baseStart_3509811 : Nat := 118140960795 + 3509811 * 2 ^ 59
def prefixEnd_3509811 : Nat := 4983230072969 + 3 ^ 40 * 3509811 * 2
def baseEnd_3509811 : Nat := 1802220049437672582021179

theorem tailTrace_3509811 : CollatzResearch.WordTrace tailWord_3509811 prefixEnd_3509811 1802220049437672582021179 := by
  unfold tailWord_3509811
  simp only [CollatzResearch.WordTrace]
  refine ⟨128013323887561649841009287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85342215925041099894006191 128013323887561649841009287)
  ·
    refine ⟨192019985831342474761513931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128013323887561649841009287 192019985831342474761513931)
    ·
      refine ⟨288029978747013712142270897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192019985831342474761513931 288029978747013712142270897)
      ·
        refine ⟨216022484060260284106703173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288029978747013712142270897 216022484060260284106703173)
        ·
          refine ⟨40504215761298803270006845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216022484060260284106703173 40504215761298803270006845)
          ·
            refine ⟨15189080910487051226252567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40504215761298803270006845 15189080910487051226252567)
            ·
              refine ⟨22783621365730576839378851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15189080910487051226252567 22783621365730576839378851)
              ·
                refine ⟨34175432048595865259068277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22783621365730576839378851 34175432048595865259068277)
                ·
                  refine ⟨3203946754555862368037651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34175432048595865259068277 3203946754555862368037651)
                  ·
                    refine ⟨4805920131833793552056477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3203946754555862368037651 4805920131833793552056477)
                    ·
                      refine ⟨1802220049437672582021179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4805920131833793552056477 1802220049437672582021179)
                      ·
                        rfl

theorem cell23_3509811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_3509811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509811 prefixEnd_3509811 := by exact prefixLift 3509811
  have htrace : WordTrace (prefixWord ++ tailWord_3509811) baseStart_3509811 baseEnd_3509811 := by
    simpa [prefixWord, tailWord_3509811, baseEnd_3509811] using wordTrace_append hprefix tailTrace_3509811
  have hstable : (prefixWord ++ tailWord_3509811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509811).length < 2 ^ (prefixWord ++ tailWord_3509811).sum := by decide
  have hdescent : baseEnd_3509811 < baseStart_3509811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509861 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_3509861 : Nat := 118140960795 + 3509861 * 2 ^ 59
def prefixEnd_3509861 : Nat := 4983230072969 + 3 ^ 40 * 3509861 * 2
def baseEnd_3509861 : Nat := 600748574490132462131983

theorem tailTrace_3509861 : CollatzResearch.WordTrace tailWord_3509861 prefixEnd_3509861 600748574490132462131983 := by
  unfold tailWord_3509861
  simp only [CollatzResearch.WordTrace]
  refine ⟨128015147537380508380329437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85343431691587005586886291 128015147537380508380329437)
  ·
    refine ⟨48005680326517690642623539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128015147537380508380329437 48005680326517690642623539)
    ·
      refine ⟨72008520489776535963935309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48005680326517690642623539 72008520489776535963935309)
      ·
        refine ⟨27003195183666200986475741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72008520489776535963935309 27003195183666200986475741)
        ·
          refine ⟨10126198193874825369928403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27003195183666200986475741 10126198193874825369928403)
          ·
            refine ⟨15189297290812238054892605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10126198193874825369928403 15189297290812238054892605)
            ·
              refine ⟨5695986484054589270584727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15189297290812238054892605 5695986484054589270584727)
              ·
                refine ⟨8543979726081883905877091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695986484054589270584727 8543979726081883905877091)
                ·
                  refine ⟨12815969589122825858815637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8543979726081883905877091 12815969589122825858815637)
                  ·
                    refine ⟨600748574490132462131983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12815969589122825858815637 600748574490132462131983)
                    ·
                      rfl

theorem cell23_3509861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_3509861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509861 prefixEnd_3509861 := by exact prefixLift 3509861
  have htrace : WordTrace (prefixWord ++ tailWord_3509861) baseStart_3509861 baseEnd_3509861 := by
    simpa [prefixWord, tailWord_3509861, baseEnd_3509861] using wordTrace_append hprefix tailTrace_3509861
  have hstable : (prefixWord ++ tailWord_3509861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509861).length < 2 ^ (prefixWord ++ tailWord_3509861).sum := by decide
  have hdescent : baseEnd_3509861 < baseStart_3509861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509878 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3509878 : Nat := 118140960795 + 3509878 * 2 ^ 59
def prefixEnd_3509878 : Nat := 4983230072969 + 3 ^ 40 * 3509878 * 2
def baseEnd_3509878 : Nat := 600751484213841273294457

theorem tailTrace_3509878 : CollatzResearch.WordTrace tailWord_3509878 prefixEnd_3509878 600751484213841273294457 := by
  unfold tailWord_3509878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000985473644932517731143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85343845052212613522465525 8000985473644932517731143)
  ·
    refine ⟨12001478210467398776596715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000985473644932517731143 12001478210467398776596715)
    ·
      refine ⟨18002217315701098164895073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12001478210467398776596715 18002217315701098164895073)
      ·
        refine ⟨13501662986775823623671305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18002217315701098164895073 13501662986775823623671305)
        ·
          refine ⟨10126247240081867717753479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13501662986775823623671305 10126247240081867717753479)
          ·
            refine ⟨15189370860122801576630219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10126247240081867717753479 15189370860122801576630219)
            ·
              refine ⟨22784056290184202364945329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15189370860122801576630219 22784056290184202364945329)
              ·
                refine ⟨17088042217638151773708997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22784056290184202364945329 17088042217638151773708997)
                ·
                  refine ⟨3204007915807153457570437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17088042217638151773708997 3204007915807153457570437)
                  ·
                    refine ⟨600751484213841273294457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204007915807153457570437 600751484213841273294457)
                    ·
                      rfl

theorem cell23_3509878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3509878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509878 prefixEnd_3509878 := by exact prefixLift 3509878
  have htrace : WordTrace (prefixWord ++ tailWord_3509878) baseStart_3509878 baseEnd_3509878 := by
    simpa [prefixWord, tailWord_3509878, baseEnd_3509878] using wordTrace_append hprefix tailTrace_3509878
  have hstable : (prefixWord ++ tailWord_3509878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509878).length < 2 ^ (prefixWord ++ tailWord_3509878).sum := by decide
  have hdescent : baseEnd_3509878 < baseStart_3509878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509902 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3509902 : Nat := 118140960795 + 3509902 * 2 ^ 59
def prefixEnd_3509902 : Nat := 4983230072969 + 3 ^ 40 * 3509902 * 2
def baseEnd_3509902 : Nat := 1802266776177231725983261

theorem tailTrace_3509902 : CollatzResearch.WordTrace tailWord_3509902 prefixEnd_3509902 1802266776177231725983261 := by
  unfold tailWord_3509902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16002080366278996547821495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85344428620154648255047973 16002080366278996547821495)
  ·
    refine ⟨24003120549418494821732243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16002080366278996547821495 24003120549418494821732243)
    ·
      refine ⟨36004680824127742232598365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24003120549418494821732243 36004680824127742232598365)
      ·
        refine ⟨13501755309047903337224387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36004680824127742232598365 13501755309047903337224387)
        ·
          refine ⟨20252632963571855005836581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13501755309047903337224387 20252632963571855005836581)
          ·
            refine ⟨3797368680669722813594359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20252632963571855005836581 3797368680669722813594359)
            ·
              refine ⟨5696053021004584220391539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797368680669722813594359 5696053021004584220391539)
              ·
                refine ⟨8544079531506876330587309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696053021004584220391539 8544079531506876330587309)
                ·
                  refine ⟨3204029824315078623970241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8544079531506876330587309 3204029824315078623970241)
                  ·
                    refine ⟨2403022368236308967977681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3204029824315078623970241 2403022368236308967977681)
                    ·
                      refine ⟨1802266776177231725983261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403022368236308967977681 1802266776177231725983261)
                      ·
                        rfl

theorem cell23_3509902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3509902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509902 prefixEnd_3509902 := by exact prefixLift 3509902
  have htrace : WordTrace (prefixWord ++ tailWord_3509902) baseStart_3509902 baseEnd_3509902 := by
    simpa [prefixWord, tailWord_3509902, baseEnd_3509902] using wordTrace_append hprefix tailTrace_3509902
  have hstable : (prefixWord ++ tailWord_3509902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509902).length < 2 ^ (prefixWord ++ tailWord_3509902).sum := by decide
  have hdescent : baseEnd_3509902 < baseStart_3509902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509908 : List Nat := [2, 4, 2, 2, 2, 1, 2, 8]
def baseStart_3509908 : Nat := 118140960795 + 3509908 * 2 ^ 59
def prefixEnd_3509908 : Nat := 4983230072969 + 3 ^ 40 * 3509908 * 2
def baseEnd_3509908 : Nat := 66750735446709581574379

theorem tailTrace_3509908 : CollatzResearch.WordTrace tailWord_3509908 prefixEnd_3509908 66750735446709581574379 := by
  unfold tailWord_3509908
  simp only [CollatzResearch.WordTrace]
  refine ⟨64008430884105117703645189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85344574512140156938193585 64008430884105117703645189)
  ·
    refine ⟨12001580790769709569433473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64008430884105117703645189 12001580790769709569433473)
    ·
      refine ⟨9001185593077282177075105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12001580790769709569433473 9001185593077282177075105)
      ·
        refine ⟨6750889194807961632806329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9001185593077282177075105 6750889194807961632806329)
        ·
          refine ⟨5063166896105971224604747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6750889194807961632806329 5063166896105971224604747)
          ·
            refine ⟨7594750344158956836907121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063166896105971224604747 7594750344158956836907121)
            ·
              refine ⟨5696062758119217627680341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7594750344158956836907121 5696062758119217627680341)
              ·
                refine ⟨66750735446709581574379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5696062758119217627680341 66750735446709581574379)
                ·
                  rfl

theorem cell23_3509908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 8].length) (baseStart_3509908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509908 prefixEnd_3509908 := by exact prefixLift 3509908
  have htrace : WordTrace (prefixWord ++ tailWord_3509908) baseStart_3509908 baseEnd_3509908 := by
    simpa [prefixWord, tailWord_3509908, baseEnd_3509908] using wordTrace_append hprefix tailTrace_3509908
  have hstable : (prefixWord ++ tailWord_3509908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509908).length < 2 ^ (prefixWord ++ tailWord_3509908).sum := by decide
  have hdescent : baseEnd_3509908 < baseStart_3509908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3509975 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_3509975 : Nat := 118140960795 + 3509975 * 2 ^ 59
def prefixEnd_3509975 : Nat := 4983230072969 + 3 ^ 40 * 3509975 * 2
def baseEnd_3509975 : Nat := 1802304260265009940370425

theorem tailTrace_3509975 : CollatzResearch.WordTrace tailWord_3509975 prefixEnd_3509975 1802304260265009940370425 := by
  unfold tailWord_3509975
  simp only [CollatzResearch.WordTrace]
  refine ⟨128019305458967505849979379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85346203639311670566652919 128019305458967505849979379)
  ·
    refine ⟨192028958188451258774969069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128019305458967505849979379 192028958188451258774969069)
    ·
      refine ⟨72010859320669222040613401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192028958188451258774969069 72010859320669222040613401)
      ·
        refine ⟨54008144490501916530460051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72010859320669222040613401 54008144490501916530460051)
        ·
          refine ⟨81012216735752874795690077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54008144490501916530460051 81012216735752874795690077)
          ·
            refine ⟨30379581275907328048383779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81012216735752874795690077 30379581275907328048383779)
            ·
              refine ⟨45569371913860992072575669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30379581275907328048383779 45569371913860992072575669)
              ·
                refine ⟨4272128616924468006803969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45569371913860992072575669 4272128616924468006803969)
                ·
                  refine ⟨3204096462693351005102977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4272128616924468006803969 3204096462693351005102977)
                  ·
                    refine ⟨2403072347020013253827233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3204096462693351005102977 2403072347020013253827233)
                    ·
                      refine ⟨1802304260265009940370425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403072347020013253827233 1802304260265009940370425)
                      ·
                        rfl

theorem cell23_3509975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_3509975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3509975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3509975 prefixEnd_3509975 := by exact prefixLift 3509975
  have htrace : WordTrace (prefixWord ++ tailWord_3509975) baseStart_3509975 baseEnd_3509975 := by
    simpa [prefixWord, tailWord_3509975, baseEnd_3509975] using wordTrace_append hprefix tailTrace_3509975
  have hstable : (prefixWord ++ tailWord_3509975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3509975).length < 2 ^ (prefixWord ++ tailWord_3509975).sum := by decide
  have hdescent : baseEnd_3509975 < baseStart_3509975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3509975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510031 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_3510031 : Nat := 118140960795 + 3510031 * 2 ^ 59
def prefixEnd_3510031 : Nat := 4983230072969 + 3 ^ 40 * 3510031 * 2
def baseEnd_3510031 : Nat := 1802333015181661721270167

theorem tailTrace_3510031 : CollatzResearch.WordTrace tailWord_3510031 prefixEnd_3510031 1802333015181661721270167 := by
  unfold tailWord_3510031
  simp only [CollatzResearch.WordTrace]
  refine ⟨128021347946764627414017947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85347565297843084942678631 128021347946764627414017947)
  ·
    refine ⟨192032021920146941121026921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128021347946764627414017947 192032021920146941121026921)
    ·
      refine ⟨144024016440110205840770191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192032021920146941121026921 144024016440110205840770191)
      ·
        refine ⟨216036024660165308761155287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144024016440110205840770191 216036024660165308761155287)
        ·
          refine ⟨324054036990247963141732931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216036024660165308761155287 324054036990247963141732931)
          ·
            refine ⟨486081055485371944712599397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324054036990247963141732931 486081055485371944712599397)
            ·
              refine ⟨91140197903507239633612387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 486081055485371944712599397 91140197903507239633612387)
              ·
                refine ⟨136710296855260859450418581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91140197903507239633612387 136710296855260859450418581)
                ·
                  refine ⟨6408295165090352786738371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136710296855260859450418581 6408295165090352786738371)
                  ·
                    refine ⟨9612442747635529180107557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6408295165090352786738371 9612442747635529180107557)
                    ·
                      refine ⟨1802333015181661721270167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9612442747635529180107557 1802333015181661721270167)
                      ·
                        rfl

theorem cell23_3510031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_3510031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510031 prefixEnd_3510031 := by exact prefixLift 3510031
  have htrace : WordTrace (prefixWord ++ tailWord_3510031) baseStart_3510031 baseEnd_3510031 := by
    simpa [prefixWord, tailWord_3510031, baseEnd_3510031] using wordTrace_append hprefix tailTrace_3510031
  have hstable : (prefixWord ++ tailWord_3510031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510031).length < 2 ^ (prefixWord ++ tailWord_3510031).sum := by decide
  have hdescent : baseEnd_3510031 < baseStart_3510031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510048 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3510048 : Nat := 118140960795 + 3510048 * 2 ^ 59
def prefixEnd_3510048 : Nat := 4983230072969 + 3 ^ 40 * 3510048 * 2
def baseEnd_3510048 : Nat := 1802341744352788154757589

theorem tailTrace_3510048 : CollatzResearch.WordTrace tailWord_3510048 prefixEnd_3510048 1802341744352788154757589 := by
  unfold tailWord_3510048
  simp only [CollatzResearch.WordTrace]
  refine ⟨64010983993851519658693399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85347978658468692878257865 64010983993851519658693399)
  ·
    refine ⟨96016475990777279488040099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64010983993851519658693399 96016475990777279488040099)
    ·
      refine ⟨144024713986165919232060149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96016475990777279488040099 144024713986165919232060149)
      ·
        refine ⟨13502316936203054928005639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144024713986165919232060149 13502316936203054928005639)
        ·
          refine ⟨20253475404304582392008459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13502316936203054928005639 20253475404304582392008459)
          ·
            refine ⟨30380213106456873588012689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20253475404304582392008459 30380213106456873588012689)
            ·
              refine ⟨22785159829842655191009517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30380213106456873588012689 22785159829842655191009517)
              ·
                refine ⟨8544434936190995696628569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22785159829842655191009517 8544434936190995696628569)
                ·
                  refine ⟨6408326202143246772471427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8544434936190995696628569 6408326202143246772471427)
                  ·
                    refine ⟨9612489303214870158707141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6408326202143246772471427 9612489303214870158707141)
                    ·
                      refine ⟨1802341744352788154757589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9612489303214870158707141 1802341744352788154757589)
                      ·
                        rfl

theorem cell23_3510048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3510048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510048 prefixEnd_3510048 := by exact prefixLift 3510048
  have htrace : WordTrace (prefixWord ++ tailWord_3510048) baseStart_3510048 baseEnd_3510048 := by
    simpa [prefixWord, tailWord_3510048, baseEnd_3510048] using wordTrace_append hprefix tailTrace_3510048
  have hstable : (prefixWord ++ tailWord_3510048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510048).length < 2 ^ (prefixWord ++ tailWord_3510048).sum := by decide
  have hdescent : baseEnd_3510048 < baseStart_3510048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510088 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 6]
def baseStart_3510088 : Nat := 118140960795 + 3510088 * 2 ^ 59
def prefixEnd_3510088 : Nat := 4983230072969 + 3 ^ 40 * 3510088 * 2
def baseEnd_3510088 : Nat := 200262475953218666473045

theorem tailTrace_3510088 : CollatzResearch.WordTrace tailWord_3510088 prefixEnd_3510088 200262475953218666473045 := by
  unfold tailWord_3510088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64011713453779063074421459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85348951271705417432561945 64011713453779063074421459)
  ·
    refine ⟨96017570180668594611632189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64011713453779063074421459 96017570180668594611632189)
    ·
      refine ⟨36006588817750722979362071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96017570180668594611632189 36006588817750722979362071)
      ·
        refine ⟨54009883226626084469043107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36006588817750722979362071 54009883226626084469043107)
        ·
          refine ⟨81014824839939126703564661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54009883226626084469043107 81014824839939126703564661)
          ·
            refine ⟨7595139828744293128459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81014824839939126703564661 7595139828744293128459187)
            ·
              refine ⟨11392709743116439692688781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595139828744293128459187 11392709743116439692688781)
              ·
                refine ⟨4272266153668664884758293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11392709743116439692688781 4272266153668664884758293)
                ·
                  refine ⟨200262475953218666473045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4272266153668664884758293 200262475953218666473045)
                  ·
                    rfl

theorem cell23_3510088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_3510088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510088 prefixEnd_3510088 := by exact prefixLift 3510088
  have htrace : WordTrace (prefixWord ++ tailWord_3510088) baseStart_3510088 baseEnd_3510088 := by
    simpa [prefixWord, tailWord_3510088, baseEnd_3510088] using wordTrace_append hprefix tailTrace_3510088
  have hstable : (prefixWord ++ tailWord_3510088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510088).length < 2 ^ (prefixWord ++ tailWord_3510088).sum := by decide
  have hdescent : baseEnd_3510088 < baseStart_3510088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510122 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_3510122 : Nat := 118140960795 + 3510122 * 2 ^ 59
def prefixEnd_3510122 : Nat := 4983230072969 + 3 ^ 40 * 3510122 * 2
def baseEnd_3510122 : Nat := 200264415769024540581361

theorem tailTrace_3510122 : CollatzResearch.WordTrace tailWord_3510122 prefixEnd_3510122 200264415769024540581361 := by
  unfold tailWord_3510122
  simp only [CollatzResearch.WordTrace]
  refine ⟨32006166747358737488895155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85349777992956633303720413 32006166747358737488895155)
  ·
    refine ⟨48009250121038106233342733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32006166747358737488895155 48009250121038106233342733)
    ·
      refine ⟨18003468795389289837503525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48009250121038106233342733 18003468795389289837503525)
      ·
        refine ⟨3375650399135491844531911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18003468795389289837503525 3375650399135491844531911)
        ·
          refine ⟨5063475598703237766797867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375650399135491844531911 5063475598703237766797867)
          ·
            refine ⟨7595213398054856650196801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063475598703237766797867 7595213398054856650196801)
            ·
              refine ⟨5696410048541142487647601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7595213398054856650196801 5696410048541142487647601)
              ·
                refine ⟨4272307536405856865735701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5696410048541142487647601 4272307536405856865735701)
                ·
                  refine ⟨200264415769024540581361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4272307536405856865735701 200264415769024540581361)
                  ·
                    rfl

theorem cell23_3510122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_3510122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510122 prefixEnd_3510122 := by exact prefixLift 3510122
  have htrace : WordTrace (prefixWord ++ tailWord_3510122) baseStart_3510122 baseEnd_3510122 := by
    simpa [prefixWord, tailWord_3510122, baseEnd_3510122] using wordTrace_append hprefix tailTrace_3510122
  have hstable : (prefixWord ++ tailWord_3510122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510122).length < 2 ^ (prefixWord ++ tailWord_3510122).sum := by decide
  have hdescent : baseEnd_3510122 < baseStart_3510122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510126 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3510126 : Nat := 118140960795 + 3510126 * 2 ^ 59
def prefixEnd_3510126 : Nat := 4983230072969 + 3 ^ 40 * 3510126 * 2
def baseEnd_3510126 : Nat := 600793931947946283194077

theorem tailTrace_3510126 : CollatzResearch.WordTrace tailWord_3510126 prefixEnd_3510126 600793931947946283194077 := by
  unfold tailWord_3510126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003101610177557329840779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85349875254280305759150821 16003101610177557329840779)
  ·
    refine ⟨24004652415266335994761169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16003101610177557329840779 24004652415266335994761169)
    ·
      refine ⟨18003489311449751996070877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24004652415266335994761169 18003489311449751996070877)
      ·
        refine ⟨6751308491793656998526579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18003489311449751996070877 6751308491793656998526579)
        ·
          refine ⟨10126962737690485497789869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751308491793656998526579 10126962737690485497789869)
          ·
            refine ⟨3797611026633932061671201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10126962737690485497789869 3797611026633932061671201)
            ·
              refine ⟨2848208269975449046253401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797611026633932061671201 2848208269975449046253401)
              ·
                refine ⟨2136156202481586784690051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848208269975449046253401 2136156202481586784690051)
                ·
                  refine ⟨3204234303722380177035077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136156202481586784690051 3204234303722380177035077)
                  ·
                    refine ⟨600793931947946283194077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204234303722380177035077 600793931947946283194077)
                    ·
                      rfl

theorem cell23_3510126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3510126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510126 prefixEnd_3510126 := by exact prefixLift 3510126
  have htrace : WordTrace (prefixWord ++ tailWord_3510126) baseStart_3510126 baseEnd_3510126 := by
    simpa [prefixWord, tailWord_3510126, baseEnd_3510126] using wordTrace_append hprefix tailTrace_3510126
  have hstable : (prefixWord ++ tailWord_3510126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510126).length < 2 ^ (prefixWord ++ tailWord_3510126).sum := by decide
  have hdescent : baseEnd_3510126 < baseStart_3510126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510131 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 5, 6]
def baseStart_3510131 : Nat := 118140960795 + 3510131 * 2 ^ 59
def prefixEnd_3510131 : Nat := 4983230072969 + 3 ^ 40 * 3510131 * 2
def baseEnd_3510131 : Nat := 600794787749037110006569

theorem tailTrace_3510131 : CollatzResearch.WordTrace tailWord_3510131 prefixEnd_3510131 600794787749037110006569 := by
  unfold tailWord_3510131
  simp only [CollatzResearch.WordTrace]
  refine ⟨128024995246402344492658247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85349996830934896328438831 128024995246402344492658247)
  ·
    refine ⟨192037492869603516738987371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128024995246402344492658247 192037492869603516738987371)
    ·
      refine ⟨288056239304405275108481057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192037492869603516738987371 288056239304405275108481057)
      ·
        refine ⟨216042179478303956331360793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288056239304405275108481057 216042179478303956331360793)
        ·
          refine ⟨162031634608727967248520595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216042179478303956331360793 162031634608727967248520595)
          ·
            refine ⟨243047451913091950872780893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162031634608727967248520595 243047451913091950872780893)
            ·
              refine ⟨91142794467409481577292835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243047451913091950872780893 91142794467409481577292835)
              ·
                refine ⟨136714191701114222365939253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91142794467409481577292835 136714191701114222365939253)
                ·
                  refine ⟨12816955471979458346806805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136714191701114222365939253 12816955471979458346806805)
                  ·
                    refine ⟨600794787749037110006569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12816955471979458346806805 600794787749037110006569)
                    ·
                      rfl

theorem cell23_3510131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_3510131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510131 prefixEnd_3510131 := by exact prefixLift 3510131
  have htrace : WordTrace (prefixWord ++ tailWord_3510131) baseStart_3510131 baseEnd_3510131 := by
    simpa [prefixWord, tailWord_3510131, baseEnd_3510131] using wordTrace_append hprefix tailTrace_3510131
  have hstable : (prefixWord ++ tailWord_3510131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510131).length < 2 ^ (prefixWord ++ tailWord_3510131).sum := by decide
  have hdescent : baseEnd_3510131 < baseStart_3510131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510138 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_3510138 : Nat := 118140960795 + 3510138 * 2 ^ 59
def prefixEnd_3510138 : Nat := 4983230072969 + 3 ^ 40 * 3510138 * 2
def baseEnd_3510138 : Nat := 1802387957611692802632175

theorem tailTrace_3510138 : CollatzResearch.WordTrace tailWord_3510138 prefixEnd_3510138 1802387957611692802632175 := by
  unfold tailWord_3510138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32006312639344246172040767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85350167038251323125442045 32006312639344246172040767)
  ·
    refine ⟨48009468959016369258061151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32006312639344246172040767 48009468959016369258061151)
    ·
      refine ⟨72014203438524553887091727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48009468959016369258061151 72014203438524553887091727)
      ·
        refine ⟨108021305157786830830637591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72014203438524553887091727 108021305157786830830637591)
        ·
          refine ⟨162031957736680246245956387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108021305157786830830637591 162031957736680246245956387)
          ·
            refine ⟨243047936605020369368934581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162031957736680246245956387 243047936605020369368934581)
            ·
              refine ⟨22785744056720659628337617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243047936605020369368934581 22785744056720659628337617)
              ·
                refine ⟨17089308042540494721253213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22785744056720659628337617 17089308042540494721253213)
                ·
                  refine ⟨6408490515952685520469955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17089308042540494721253213 6408490515952685520469955)
                  ·
                    refine ⟨9612735773929028280704933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6408490515952685520469955 9612735773929028280704933)
                    ·
                      refine ⟨1802387957611692802632175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9612735773929028280704933 1802387957611692802632175)
                      ·
                        rfl

theorem cell23_3510138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_3510138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510138 prefixEnd_3510138 := by exact prefixLift 3510138
  have htrace : WordTrace (prefixWord ++ tailWord_3510138) baseStart_3510138 baseEnd_3510138 := by
    simpa [prefixWord, tailWord_3510138, baseEnd_3510138] using wordTrace_append hprefix tailTrace_3510138
  have hstable : (prefixWord ++ tailWord_3510138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510138).length < 2 ^ (prefixWord ++ tailWord_3510138).sum := by decide
  have hdescent : baseEnd_3510138 < baseStart_3510138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510148 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3510148 : Nat := 118140960795 + 3510148 * 2 ^ 59
def prefixEnd_3510148 : Nat := 4983230072969 + 3 ^ 40 * 3510148 * 2
def baseEnd_3510148 : Nat := 600797697472745921169043

theorem tailTrace_3510148 : CollatzResearch.WordTrace tailWord_3510148 prefixEnd_3510148 600797697472745921169043 := by
  unfold tailWord_3510148
  simp only [CollatzResearch.WordTrace]
  refine ⟨64012807643670378198013549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85350410191560504264018065 64012807643670378198013549)
  ·
    refine ⟨24004802866376391824255081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64012807643670378198013549 24004802866376391824255081)
    ·
      refine ⟨18003602149782293868191311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24004802866376391824255081 18003602149782293868191311)
      ·
        refine ⟨27005403224673440802286967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18003602149782293868191311 27005403224673440802286967)
        ·
          refine ⟨40508104837010161203430451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27005403224673440802286967 40508104837010161203430451)
          ·
            refine ⟨60762157255515241805145677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40508104837010161203430451 60762157255515241805145677)
            ·
              refine ⟨22785808970818215676929629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60762157255515241805145677 22785808970818215676929629)
              ·
                refine ⟨8544678364056830878848611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22785808970818215676929629 8544678364056830878848611)
                ·
                  refine ⟨12817017546085246318272917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8544678364056830878848611 12817017546085246318272917)
                  ·
                    refine ⟨600797697472745921169043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12817017546085246318272917 600797697472745921169043)
                    ·
                      rfl

theorem cell23_3510148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3510148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510148 prefixEnd_3510148 := by exact prefixLift 3510148
  have htrace : WordTrace (prefixWord ++ tailWord_3510148) baseStart_3510148 baseEnd_3510148 := by
    simpa [prefixWord, tailWord_3510148, baseEnd_3510148] using wordTrace_append hprefix tailTrace_3510148
  have hstable : (prefixWord ++ tailWord_3510148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510148).length < 2 ^ (prefixWord ++ tailWord_3510148).sum := by decide
  have hdescent : baseEnd_3510148 < baseStart_3510148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510161 : List Nat := [1, 2, 2, 1, 1, 1, 4, 11]
def baseStart_3510161 : Nat := 118140960795 + 3510161 * 2 ^ 59
def prefixEnd_3510161 : Nat := 4983230072969 + 3 ^ 40 * 3510161 * 2
def baseEnd_3510161 : Nat := 66755546950620230097947

theorem tailTrace_3510161 : CollatzResearch.WordTrace tailWord_3510161 prefixEnd_3510161 66755546950620230097947 := by
  unfold tailWord_3510161
  simp only [CollatzResearch.WordTrace]
  refine ⟨128026089436293659616250337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85350726290862439744166891 128026089436293659616250337)
  ·
    refine ⟨96019567077220244712187753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128026089436293659616250337 96019567077220244712187753)
    ·
      refine ⟨72014675307915183534140815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96019567077220244712187753 72014675307915183534140815)
      ·
        refine ⟨108022012961872775301211223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72014675307915183534140815 108022012961872775301211223)
        ·
          refine ⟨162033019442809162951816835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108022012961872775301211223 162033019442809162951816835)
          ·
            refine ⟨243049529164213744427725253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162033019442809162951816835 243049529164213744427725253)
            ·
              refine ⟨45571786718290077080198485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243049529164213744427725253 45571786718290077080198485)
              ·
                refine ⟨66755546950620230097947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 45571786718290077080198485 66755546950620230097947)
                ·
                  rfl

theorem cell23_3510161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 11].length) (baseStart_3510161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510161 prefixEnd_3510161 := by exact prefixLift 3510161
  have htrace : WordTrace (prefixWord ++ tailWord_3510161) baseStart_3510161 baseEnd_3510161 := by
    simpa [prefixWord, tailWord_3510161, baseEnd_3510161] using wordTrace_append hprefix tailTrace_3510161
  have hstable : (prefixWord ++ tailWord_3510161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510161).length < 2 ^ (prefixWord ++ tailWord_3510161).sum := by decide
  have hdescent : baseEnd_3510161 < baseStart_3510161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510172 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3510172 : Nat := 118140960795 + 3510172 * 2 ^ 59
def prefixEnd_3510172 : Nat := 4983230072969 + 3 ^ 40 * 3510172 * 2
def baseEnd_3510172 : Nat := 1802405415953945669607019

theorem tailTrace_3510172 : CollatzResearch.WordTrace tailWord_3510172 prefixEnd_3510172 1802405415953945669607019 := by
  unfold tailWord_3510172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64013245319626904247450385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85350993759502538996600513 64013245319626904247450385)
  ·
    refine ⟨48009933989720178185587789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64013245319626904247450385 48009933989720178185587789)
    ·
      refine ⟨18003725246145066819595421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48009933989720178185587789 18003725246145066819595421)
      ·
        refine ⟨6751396967304400057348283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18003725246145066819595421 6751396967304400057348283)
        ·
          refine ⟨10127095450956600086022425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751396967304400057348283 10127095450956600086022425)
          ·
            refine ⟨7595321588217450064516819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127095450956600086022425 7595321588217450064516819)
            ·
              refine ⟨11392982382326175096775229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595321588217450064516819 11392982382326175096775229)
              ·
                refine ⟨4272368393372315661290711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11392982382326175096775229 4272368393372315661290711)
                ·
                  refine ⟨6408552590058473491936067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272368393372315661290711 6408552590058473491936067)
                  ·
                    refine ⟨9612828885087710237904101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6408552590058473491936067 9612828885087710237904101)
                    ·
                      refine ⟨1802405415953945669607019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9612828885087710237904101 1802405415953945669607019)
                      ·
                        rfl

theorem cell23_3510172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3510172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510172 prefixEnd_3510172 := by exact prefixLift 3510172
  have htrace : WordTrace (prefixWord ++ tailWord_3510172) baseStart_3510172 baseEnd_3510172 := by
    simpa [prefixWord, tailWord_3510172, baseEnd_3510172] using wordTrace_append hprefix tailTrace_3510172
  have hstable : (prefixWord ++ tailWord_3510172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510172).length < 2 ^ (prefixWord ++ tailWord_3510172).sum := by decide
  have hdescent : baseEnd_3510172 < baseStart_3510172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510218 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3510218 : Nat := 118140960795 + 3510218 * 2 ^ 59
def prefixEnd_3510218 : Nat := 4983230072969 + 3 ^ 40 * 3510218 * 2
def baseEnd_3510218 : Nat := 1802429036064052489631807

theorem tailTrace_3510218 : CollatzResearch.WordTrace tailWord_3510218 prefixEnd_3510218 1802429036064052489631807 := by
  unfold tailWord_3510218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32007042099271789587768827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85352112264724772234050205 32007042099271789587768827)
  ·
    refine ⟨48010563148907684381653241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32007042099271789587768827 48010563148907684381653241)
    ·
      refine ⟨36007922361680763286239931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48010563148907684381653241 36007922361680763286239931)
      ·
        refine ⟨54011883542521144929359897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36007922361680763286239931 54011883542521144929359897)
        ·
          refine ⟨40508912656890858697019923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54011883542521144929359897 40508912656890858697019923)
          ·
            refine ⟨60763368985336288045529885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40508912656890858697019923 60763368985336288045529885)
            ·
              refine ⟨22786263369501108017073707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60763368985336288045529885 22786263369501108017073707)
              ·
                refine ⟨34179395054251662025610561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22786263369501108017073707 34179395054251662025610561)
                ·
                  refine ⟨25634546290688746519207921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34179395054251662025610561 25634546290688746519207921)
                  ·
                    refine ⟨19225909718016559889405941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25634546290688746519207921 19225909718016559889405941)
                    ·
                      refine ⟨1802429036064052489631807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19225909718016559889405941 1802429036064052489631807)
                      ·
                        rfl

theorem cell23_3510218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3510218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510218 prefixEnd_3510218 := by exact prefixLift 3510218
  have htrace : WordTrace (prefixWord ++ tailWord_3510218) baseStart_3510218 baseEnd_3510218 := by
    simpa [prefixWord, tailWord_3510218, baseEnd_3510218] using wordTrace_append hprefix tailTrace_3510218
  have hstable : (prefixWord ++ tailWord_3510218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510218).length < 2 ^ (prefixWord ++ tailWord_3510218).sum := by decide
  have hdescent : baseEnd_3510218 < baseStart_3510218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510232 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_3510232 : Nat := 118140960795 + 3510232 * 2 ^ 59
def prefixEnd_3510232 : Nat := 4983230072969 + 3 ^ 40 * 3510232 * 2
def baseEnd_3510232 : Nat := 1802436224793215434856743

theorem tailTrace_3510232 : CollatzResearch.WordTrace tailWord_3510232 prefixEnd_3510232 1802436224793215434856743 := by
  unfold tailWord_3510232
  simp only [CollatzResearch.WordTrace]
  refine ⟨64014339509518219371042475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85352452679357625828056633 64014339509518219371042475)
  ·
    refine ⟨96021509264277329056563713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64014339509518219371042475 96021509264277329056563713)
    ·
      refine ⟨72016131948207996792422785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96021509264277329056563713 72016131948207996792422785)
      ·
        refine ⟨54012098961155997594317089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72016131948207996792422785 54012098961155997594317089)
        ·
          refine ⟨40509074220866998195737817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54012098961155997594317089 40509074220866998195737817)
          ·
            refine ⟨30381805665650248646803363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40509074220866998195737817 30381805665650248646803363)
            ·
              refine ⟨45572708498475372970205045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30381805665650248646803363 45572708498475372970205045)
              ·
                refine ⟨4272441421732066215956723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45572708498475372970205045 4272441421732066215956723)
                ·
                  refine ⟨6408662132598099323935085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272441421732066215956723 6408662132598099323935085)
                  ·
                    refine ⟨2403248299724287246475657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6408662132598099323935085 2403248299724287246475657)
                    ·
                      refine ⟨1802436224793215434856743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403248299724287246475657 1802436224793215434856743)
                      ·
                        rfl

theorem cell23_3510232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_3510232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510232 prefixEnd_3510232 := by exact prefixLift 3510232
  have htrace : WordTrace (prefixWord ++ tailWord_3510232) baseStart_3510232 baseEnd_3510232 := by
    simpa [prefixWord, tailWord_3510232, baseEnd_3510232] using wordTrace_append hprefix tailTrace_3510232
  have hstable : (prefixWord ++ tailWord_3510232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510232).length < 2 ^ (prefixWord ++ tailWord_3510232).sum := by decide
  have hdescent : baseEnd_3510232 < baseStart_3510232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510248 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3510248 : Nat := 118140960795 + 3510248 * 2 ^ 59
def prefixEnd_3510248 : Nat := 4983230072969 + 3 ^ 40 * 3510248 * 2
def baseEnd_3510248 : Nat := 1802444440483687372256669

theorem tailTrace_3510248 : CollatzResearch.WordTrace tailWord_3510248 prefixEnd_3510248 1802444440483687372256669 := by
  unfold tailWord_3510248
  simp only [CollatzResearch.WordTrace]
  refine ⟨64014631293489236737333699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85352841724652315649778265 64014631293489236737333699)
  ·
    refine ⟨96021946940233855106000549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64014631293489236737333699 96021946940233855106000549)
    ·
      refine ⟨18004115051293847832375103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96021946940233855106000549 18004115051293847832375103)
      ·
        refine ⟨27006172576940771748562655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18004115051293847832375103 27006172576940771748562655)
        ·
          refine ⟨40509258865411157622843983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27006172576940771748562655 40509258865411157622843983)
          ·
            refine ⟨60763888298116736434265975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40509258865411157622843983 60763888298116736434265975)
            ·
              refine ⟨91145832447175104651398963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60763888298116736434265975 91145832447175104651398963)
              ·
                refine ⟨136718748670762656977098445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91145832447175104651398963 136718748670762656977098445)
                ·
                  refine ⟨51269530751535996366411917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136718748670762656977098445 51269530751535996366411917)
                  ·
                    refine ⟨19226074031825998637404469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51269530751535996366411917 19226074031825998637404469)
                    ·
                      refine ⟨1802444440483687372256669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19226074031825998637404469 1802444440483687372256669)
                      ·
                        rfl

theorem cell23_3510248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3510248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510248 prefixEnd_3510248 := by exact prefixLift 3510248
  have htrace : WordTrace (prefixWord ++ tailWord_3510248) baseStart_3510248 baseEnd_3510248 := by
    simpa [prefixWord, tailWord_3510248, baseEnd_3510248] using wordTrace_append hprefix tailTrace_3510248
  have hstable : (prefixWord ++ tailWord_3510248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510248).length < 2 ^ (prefixWord ++ tailWord_3510248).sum := by decide
  have hdescent : baseEnd_3510248 < baseStart_3510248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510268 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 9]
def baseStart_3510268 : Nat := 118140960795 + 3510268 * 2 ^ 59
def prefixEnd_3510268 : Nat := 4983230072969 + 3 ^ 40 * 3510268 * 2
def baseEnd_3510268 : Nat := 200272745566308588222953

theorem tailTrace_3510268 : CollatzResearch.WordTrace tailWord_3510268 prefixEnd_3510268 200272745566308588222953 := by
  unfold tailWord_3510268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64014996023453008445197729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85353328031270677926930305 64014996023453008445197729)
  ·
    refine ⟨48011247017589756333898297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64014996023453008445197729 48011247017589756333898297)
    ·
      refine ⟨36008435263192317250423723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48011247017589756333898297 36008435263192317250423723)
      ·
        refine ⟨54012652894788475875635585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36008435263192317250423723 54012652894788475875635585)
        ·
          refine ⟨40509489671091356906726689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54012652894788475875635585 40509489671091356906726689)
          ·
            refine ⟨30382117253318517680045017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40509489671091356906726689 30382117253318517680045017)
            ·
              refine ⟨22786587939988888260033763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30382117253318517680045017 22786587939988888260033763)
              ·
                refine ⟨34179881909983332390050645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22786587939988888260033763 34179881909983332390050645)
                ·
                  refine ⟨200272745566308588222953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34179881909983332390050645 200272745566308588222953)
                  ·
                    rfl

theorem cell23_3510268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_3510268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510268 prefixEnd_3510268 := by exact prefixLift 3510268
  have htrace : WordTrace (prefixWord ++ tailWord_3510268) baseStart_3510268 baseEnd_3510268 := by
    simpa [prefixWord, tailWord_3510268, baseEnd_3510268] using wordTrace_append hprefix tailTrace_3510268
  have hstable : (prefixWord ++ tailWord_3510268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510268).length < 2 ^ (prefixWord ++ tailWord_3510268).sum := by decide
  have hdescent : baseEnd_3510268 < baseStart_3510268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510345 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_3510345 : Nat := 118140960795 + 3510345 * 2 ^ 59
def prefixEnd_3510345 : Nat := 4983230072969 + 3 ^ 40 * 3510345 * 2
def baseEnd_3510345 : Nat := 600831416035724497581241

theorem tailTrace_3510345 : CollatzResearch.WordTrace tailWord_3510345 prefixEnd_3510345 600831416035724497581241 := by
  unfold tailWord_3510345
  simp only [CollatzResearch.WordTrace]
  refine ⟨128032800467627059040948489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85355200311751372693965659 128032800467627059040948489)
  ·
    refine ⟨96024600350720294280711367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128032800467627059040948489 96024600350720294280711367)
    ·
      refine ⟨144036900526080441421067051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96024600350720294280711367 144036900526080441421067051)
      ·
        refine ⟨216055350789120662131600577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144036900526080441421067051 216055350789120662131600577)
        ·
          refine ⟨162041513091840496598700433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216055350789120662131600577 162041513091840496598700433)
          ·
            refine ⟨121531134818880372449025325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162041513091840496598700433 121531134818880372449025325)
            ·
              refine ⟨45574175557080139668384497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121531134818880372449025325 45574175557080139668384497)
              ·
                refine ⟨34180631667810104751288373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45574175557080139668384497 34180631667810104751288373)
                ·
                  refine ⟨3204434218857197320433285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34180631667810104751288373 3204434218857197320433285)
                  ·
                    refine ⟨600831416035724497581241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204434218857197320433285 600831416035724497581241)
                    ·
                      rfl

theorem cell23_3510345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_3510345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510345 prefixEnd_3510345 := by exact prefixLift 3510345
  have htrace : WordTrace (prefixWord ++ tailWord_3510345) baseStart_3510345 baseEnd_3510345 := by
    simpa [prefixWord, tailWord_3510345, baseEnd_3510345] using wordTrace_append hprefix tailTrace_3510345
  have hstable : (prefixWord ++ tailWord_3510345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510345).length < 2 ^ (prefixWord ++ tailWord_3510345).sum := by decide
  have hdescent : baseEnd_3510345 < baseStart_3510345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510362 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_3510362 : Nat := 118140960795 + 3510362 * 2 ^ 59
def prefixEnd_3510362 : Nat := 4983230072969 + 3 ^ 40 * 3510362 * 2
def baseEnd_3510362 : Nat := 600834325759433308743715

theorem tailTrace_3510362 : CollatzResearch.WordTrace tailWord_3510362 prefixEnd_3510362 600834325759433308743715 := by
  unfold tailWord_3510362
  simp only [CollatzResearch.WordTrace]
  refine ⟨32008355127141367736079335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85355613672376980629544893 32008355127141367736079335)
  ·
    refine ⟨48012532690712051604119003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32008355127141367736079335 48012532690712051604119003)
    ·
      refine ⟨72018799036068077406178505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48012532690712051604119003 72018799036068077406178505)
      ·
        refine ⟨54014099277051058054633879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72018799036068077406178505 54014099277051058054633879)
        ·
          refine ⟨81021148915576587081950819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54014099277051058054633879 81021148915576587081950819)
          ·
            refine ⟨121531723373364880622926229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81021148915576587081950819 121531723373364880622926229)
            ·
              refine ⟨5696799533126478779199667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121531723373364880622926229 5696799533126478779199667)
              ·
                refine ⟨8545199299689718168799501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696799533126478779199667 8545199299689718168799501)
                ·
                  refine ⟨3204449737383644313299813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8545199299689718168799501 3204449737383644313299813)
                  ·
                    refine ⟨600834325759433308743715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204449737383644313299813 600834325759433308743715)
                    ·
                      rfl

theorem cell23_3510362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_3510362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510362 prefixEnd_3510362 := by exact prefixLift 3510362
  have htrace : WordTrace (prefixWord ++ tailWord_3510362) baseStart_3510362 baseEnd_3510362 := by
    simpa [prefixWord, tailWord_3510362, baseEnd_3510362] using wordTrace_append hprefix tailTrace_3510362
  have hstable : (prefixWord ++ tailWord_3510362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510362).length < 2 ^ (prefixWord ++ tailWord_3510362).sum := by decide
  have hdescent : baseEnd_3510362 < baseStart_3510362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510385 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_3510385 : Nat := 118140960795 + 3510385 * 2 ^ 59
def prefixEnd_3510385 : Nat := 4983230072969 + 3 ^ 40 * 3510385 * 2
def baseEnd_3510385 : Nat := 1802514787333353336243539

theorem tailTrace_3510385 : CollatzResearch.WordTrace tailWord_3510385 prefixEnd_3510385 1802514787333353336243539 := by
  unfold tailWord_3510385
  simp only [CollatzResearch.WordTrace]
  refine ⟨128034259387482145872404609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85356172924988097248269739 128034259387482145872404609)
  ·
    refine ⟨96025694540611609404303457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128034259387482145872404609 96025694540611609404303457)
    ·
      refine ⟨72019270905458707053227593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96025694540611609404303457 72019270905458707053227593)
      ·
        refine ⟨54014453179094030289920695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72019270905458707053227593 54014453179094030289920695)
        ·
          refine ⟨81021679768641045434881043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54014453179094030289920695 81021679768641045434881043)
          ·
            refine ⟨121532519652961568152321565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81021679768641045434881043 121532519652961568152321565)
            ·
              refine ⟨45574694869860588057120587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121532519652961568152321565 45574694869860588057120587)
              ·
                refine ⟨68362042304790882085680881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45574694869860588057120587 68362042304790882085680881)
                ·
                  refine ⟨51271531728593161564260661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68362042304790882085680881 51271531728593161564260661)
                  ·
                    refine ⟨4806706099555608896649437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51271531728593161564260661 4806706099555608896649437)
                    ·
                      refine ⟨1802514787333353336243539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4806706099555608896649437 1802514787333353336243539)
                      ·
                        rfl

theorem cell23_3510385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_3510385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510385 prefixEnd_3510385 := by exact prefixLift 3510385
  have htrace : WordTrace (prefixWord ++ tailWord_3510385) baseStart_3510385 baseEnd_3510385 := by
    simpa [prefixWord, tailWord_3510385, baseEnd_3510385] using wordTrace_append hprefix tailTrace_3510385
  have hstable : (prefixWord ++ tailWord_3510385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510385).length < 2 ^ (prefixWord ++ tailWord_3510385).sum := by decide
  have hdescent : baseEnd_3510385 < baseStart_3510385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510396 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_3510396 : Nat := 118140960795 + 3510396 * 2 ^ 59
def prefixEnd_3510396 : Nat := 4983230072969 + 3 ^ 40 * 3510396 * 2
def baseEnd_3510396 : Nat := 600840145206850931068663

theorem tailTrace_3510396 : CollatzResearch.WordTrace tailWord_3510396 prefixEnd_3510396 600840145206850931068663 := by
  unfold tailWord_3510396
  simp only [CollatzResearch.WordTrace]
  refine ⟨64017330295221147375527521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85356440393628196500703361 64017330295221147375527521)
  ·
    refine ⟨48012997721415860531645641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64017330295221147375527521 48012997721415860531645641)
    ·
      refine ⟨36009748291061895398734231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48012997721415860531645641 36009748291061895398734231)
      ·
        refine ⟨54014622436592843098101347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36009748291061895398734231 54014622436592843098101347)
        ·
          refine ⟨81021933654889264647152021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54014622436592843098101347 81021933654889264647152021)
          ·
            refine ⟨3797903140072934280335251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81021933654889264647152021 3797903140072934280335251)
            ·
              refine ⟨5696854710109401420502877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797903140072934280335251 5696854710109401420502877)
              ·
                refine ⟨2136320516291025532688579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5696854710109401420502877 2136320516291025532688579)
                ·
                  refine ⟨3204480774436538299032869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136320516291025532688579 3204480774436538299032869)
                  ·
                    refine ⟨600840145206850931068663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204480774436538299032869 600840145206850931068663)
                    ·
                      rfl

theorem cell23_3510396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_3510396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510396 prefixEnd_3510396 := by exact prefixLift 3510396
  have htrace : WordTrace (prefixWord ++ tailWord_3510396) baseStart_3510396 baseEnd_3510396 := by
    simpa [prefixWord, tailWord_3510396, baseEnd_3510396] using wordTrace_append hprefix tailTrace_3510396
  have hstable : (prefixWord ++ tailWord_3510396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510396).length < 2 ^ (prefixWord ++ tailWord_3510396).sum := by decide
  have hdescent : baseEnd_3510396 < baseStart_3510396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510426 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_3510426 : Nat := 118140960795 + 3510426 * 2 ^ 59
def prefixEnd_3510426 : Nat := 4983230072969 + 3 ^ 40 * 3510426 * 2
def baseEnd_3510426 : Nat := 200281760004465297314539

theorem tailTrace_3510426 : CollatzResearch.WordTrace tailWord_3510426 prefixEnd_3510426 200281760004465297314539 := by
  unfold tailWord_3510426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32008938695083402468661783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85357169853555739916431421 32008938695083402468661783)
  ·
    refine ⟨48013408042625103702992675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32008938695083402468661783 48013408042625103702992675)
    ·
      refine ⟨72020112063937655554489013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48013408042625103702992675 72020112063937655554489013)
      ·
        refine ⟨6751885505994155208233345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72020112063937655554489013 6751885505994155208233345)
        ·
          refine ⟨5063914129495616406175009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6751885505994155208233345 5063914129495616406175009)
          ·
            refine ⟨3797935597121712304631257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5063914129495616406175009 3797935597121712304631257)
            ·
              refine ⟨2848451697841284228473443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797935597121712304631257 2848451697841284228473443)
              ·
                refine ⟨4272677546761926342710165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848451697841284228473443 4272677546761926342710165)
                ·
                  refine ⟨200281760004465297314539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4272677546761926342710165 200281760004465297314539)
                  ·
                    rfl

theorem cell23_3510426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_3510426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510426 prefixEnd_3510426 := by exact prefixLift 3510426
  have htrace : WordTrace (prefixWord ++ tailWord_3510426) baseStart_3510426 baseEnd_3510426 := by
    simpa [prefixWord, tailWord_3510426, baseEnd_3510426] using wordTrace_append hprefix tailTrace_3510426
  have hstable : (prefixWord ++ tailWord_3510426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510426).length < 2 ^ (prefixWord ++ tailWord_3510426).sum := by decide
  have hdescent : baseEnd_3510426 < baseStart_3510426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510439 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3510439 : Nat := 118140960795 + 3510439 * 2 ^ 59
def prefixEnd_3510439 : Nat := 4983230072969 + 3 ^ 40 * 3510439 * 2
def baseEnd_3510439 : Nat := 600847505096232041656097

theorem tailTrace_3510439 : CollatzResearch.WordTrace tailWord_3510439 prefixEnd_3510439 600847505096232041656097 := by
  unfold tailWord_3510439
  simp only [CollatzResearch.WordTrace]
  refine ⟨128036228929286513094870371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85357485952857675396580247 128036228929286513094870371)
  ·
    refine ⟨192054343393929769642305557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128036228929286513094870371 192054343393929769642305557)
    ·
      refine ⟨9002547346590457951983073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192054343393929769642305557 9002547346590457951983073)
      ·
        refine ⟨6751910509942843463987305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002547346590457951983073 6751910509942843463987305)
        ·
          refine ⟨5063932882457132597990479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6751910509942843463987305 5063932882457132597990479)
          ·
            refine ⟨7595899323685698896985719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063932882457132597990479 7595899323685698896985719)
            ·
              refine ⟨11393848985528548345478579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595899323685698896985719 11393848985528548345478579)
              ·
                refine ⟨17090773478292822518217869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11393848985528548345478579 17090773478292822518217869)
                ·
                  refine ⟨6409040054359808444331701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17090773478292822518217869 6409040054359808444331701)
                  ·
                    refine ⟨600847505096232041656097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6409040054359808444331701 600847505096232041656097)
                    ·
                      rfl

theorem cell23_3510439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3510439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510439 prefixEnd_3510439 := by exact prefixLift 3510439
  have htrace : WordTrace (prefixWord ++ tailWord_3510439) baseStart_3510439 baseEnd_3510439 := by
    simpa [prefixWord, tailWord_3510439, baseEnd_3510439] using wordTrace_append hprefix tailTrace_3510439
  have hstable : (prefixWord ++ tailWord_3510439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510439).length < 2 ^ (prefixWord ++ tailWord_3510439).sum := by decide
  have hdescent : baseEnd_3510439 < baseStart_3510439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510459 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 1, 1, 4]
def baseStart_3510459 : Nat := 118140960795 + 3510459 * 2 ^ 59
def prefixEnd_3510459 : Nat := 4983230072969 + 3 ^ 40 * 3510459 * 2
def baseEnd_3510459 : Nat := 1802552784901786046718199

theorem tailTrace_3510459 : CollatzResearch.WordTrace tailWord_3510459 prefixEnd_3510459 1802552784901786046718199 := by
  unfold tailWord_3510459
  simp only [CollatzResearch.WordTrace]
  refine ⟨128036958389214056510598431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85357972259476037673732287 128036958389214056510598431)
  ·
    refine ⟨192055437583821084765897647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128036958389214056510598431 192055437583821084765897647)
    ·
      refine ⟨288083156375731627148846471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192055437583821084765897647 288083156375731627148846471)
      ·
        refine ⟨432124734563597440723269707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288083156375731627148846471 432124734563597440723269707)
        ·
          refine ⟨648187101845396161084904561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432124734563597440723269707 648187101845396161084904561)
          ·
            refine ⟨486140326384047120813678421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648187101845396161084904561 486140326384047120813678421)
            ·
              refine ⟨2848478474906526098517647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 486140326384047120813678421 2848478474906526098517647)
              ·
                refine ⟨4272717712359789147776471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848478474906526098517647 4272717712359789147776471)
                ·
                  refine ⟨6409076568539683721664707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272717712359789147776471 6409076568539683721664707)
                  ·
                    refine ⟨9613614852809525582497061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409076568539683721664707 9613614852809525582497061)
                    ·
                      refine ⟨1802552784901786046718199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9613614852809525582497061 1802552784901786046718199)
                      ·
                        rfl

theorem cell23_3510459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 1, 4].length) (baseStart_3510459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510459 prefixEnd_3510459 := by exact prefixLift 3510459
  have htrace : WordTrace (prefixWord ++ tailWord_3510459) baseStart_3510459 baseEnd_3510459 := by
    simpa [prefixWord, tailWord_3510459, baseEnd_3510459] using wordTrace_append hprefix tailTrace_3510459
  have hstable : (prefixWord ++ tailWord_3510459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510459).length < 2 ^ (prefixWord ++ tailWord_3510459).sum := by decide
  have hdescent : baseEnd_3510459 < baseStart_3510459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510482 : List Nat := [3, 2, 2, 2, 1, 2, 3, 8]
def baseStart_3510482 : Nat := 118140960795 + 3510482 * 2 ^ 59
def prefixEnd_3510482 : Nat := 4983230072969 + 3 ^ 40 * 3510482 * 2
def baseEnd_3510482 : Nat := 66761651665068128027059

theorem tailTrace_3510482 : CollatzResearch.WordTrace tailWord_3510482 prefixEnd_3510482 66761651665068128027059 := by
  unfold tailWord_3510482
  simp only [CollatzResearch.WordTrace]
  refine ⟨32009449317032682859671425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85358531512087154292457133 32009449317032682859671425)
  ·
    refine ⟨24007086987774512144753569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32009449317032682859671425 24007086987774512144753569)
    ·
      refine ⟨18005315240830884108565177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24007086987774512144753569 18005315240830884108565177)
      ·
        refine ⟨13503986430623163081423883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18005315240830884108565177 13503986430623163081423883)
        ·
          refine ⟨20255979645934744622135825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13503986430623163081423883 20255979645934744622135825)
          ·
            refine ⟨15191984734451058466601869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20255979645934744622135825 15191984734451058466601869)
            ·
              refine ⟨5696994275419146924975701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15191984734451058466601869 5696994275419146924975701)
              ·
                refine ⟨66761651665068128027059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5696994275419146924975701 66761651665068128027059)
                ·
                  rfl

theorem cell23_3510482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_3510482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510482 prefixEnd_3510482 := by exact prefixLift 3510482
  have htrace : WordTrace (prefixWord ++ tailWord_3510482) baseStart_3510482 baseEnd_3510482 := by
    simpa [prefixWord, tailWord_3510482, baseEnd_3510482] using wordTrace_append hprefix tailTrace_3510482
  have hstable : (prefixWord ++ tailWord_3510482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510482).length < 2 ^ (prefixWord ++ tailWord_3510482).sum := by decide
  have hdescent : baseEnd_3510482 < baseStart_3510482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510486 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3510486 : Nat := 118140960795 + 3510486 * 2 ^ 59
def prefixEnd_3510486 : Nat := 4983230072969 + 3 ^ 40 * 3510486 * 2
def baseEnd_3510486 : Nat := 600855549626485813693525

theorem tailTrace_3510486 : CollatzResearch.WordTrace tailWord_3510486 prefixEnd_3510486 600855549626485813693525 := by
  unfold tailWord_3510486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002371447507265007614457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85358628773410826747887541 8002371447507265007614457)
  ·
    refine ⟨6001778585630448755710843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8002371447507265007614457 6001778585630448755710843)
    ·
      refine ⟨9002667878445673133566265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001778585630448755710843 9002667878445673133566265)
      ·
        refine ⟨6752000908834254850174699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002667878445673133566265 6752000908834254850174699)
        ·
          refine ⟨10128001363251382275262049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752000908834254850174699 10128001363251382275262049)
          ·
            refine ⟨7596001022438536706446537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128001363251382275262049 7596001022438536706446537)
            ·
              refine ⟨5697000766828902529834903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596001022438536706446537 5697000766828902529834903)
              ·
                refine ⟨8545501150243353794752355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697000766828902529834903 8545501150243353794752355)
                ·
                  refine ⟨12818251725365030692128533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545501150243353794752355 12818251725365030692128533)
                  ·
                    refine ⟨600855549626485813693525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12818251725365030692128533 600855549626485813693525)
                    ·
                      rfl

theorem cell23_3510486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3510486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510486 prefixEnd_3510486 := by exact prefixLift 3510486
  have htrace : WordTrace (prefixWord ++ tailWord_3510486) baseStart_3510486 baseEnd_3510486 := by
    simpa [prefixWord, tailWord_3510486, baseEnd_3510486] using wordTrace_append hprefix tailTrace_3510486
  have hstable : (prefixWord ++ tailWord_3510486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510486).length < 2 ^ (prefixWord ++ tailWord_3510486).sum := by decide
  have hdescent : baseEnd_3510486 < baseStart_3510486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510493 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3510493 : Nat := 118140960795 + 3510493 * 2 ^ 59
def prefixEnd_3510493 : Nat := 4983230072969 + 3 ^ 40 * 3510493 * 2
def baseEnd_3510493 : Nat := 1802570243244038913693043

theorem tailTrace_3510493 : CollatzResearch.WordTrace tailWord_3510493 prefixEnd_3510493 1802570243244038913693043 := by
  unfold tailWord_3510493
  simp only [CollatzResearch.WordTrace]
  refine ⟨128038198471090880317336133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85358798980727253544890755 128038198471090880317336133)
  ·
    refine ⟨24007162213329540059500525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128038198471090880317336133 24007162213329540059500525)
    ·
      refine ⟨9002685829998577522312697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24007162213329540059500525 9002685829998577522312697)
      ·
        refine ⟨6752014372498933141734523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002685829998577522312697 6752014372498933141734523)
        ·
          refine ⟨10128021558748399712601785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752014372498933141734523 10128021558748399712601785)
          ·
            refine ⟨7596016169061299784451339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128021558748399712601785 7596016169061299784451339)
            ·
              refine ⟨11394024253591949676677009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596016169061299784451339 11394024253591949676677009)
              ·
                refine ⟨8545518190193962257507757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394024253591949676677009 8545518190193962257507757)
                ·
                  refine ⟨3204569321322735846565409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8545518190193962257507757 3204569321322735846565409)
                  ·
                    refine ⟨2403426990992051884924057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3204569321322735846565409 2403426990992051884924057)
                    ·
                      refine ⟨1802570243244038913693043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403426990992051884924057 1802570243244038913693043)
                      ·
                        rfl

theorem cell23_3510493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3510493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510493 prefixEnd_3510493 := by exact prefixLift 3510493
  have htrace : WordTrace (prefixWord ++ tailWord_3510493) baseStart_3510493 baseEnd_3510493 := by
    simpa [prefixWord, tailWord_3510493, baseEnd_3510493] using wordTrace_append hprefix tailTrace_3510493
  have hstable : (prefixWord ++ tailWord_3510493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510493).length < 2 ^ (prefixWord ++ tailWord_3510493).sum := by decide
  have hdescent : baseEnd_3510493 < baseStart_3510493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510495 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 7]
def baseStart_3510495 : Nat := 118140960795 + 3510495 * 2 ^ 59
def prefixEnd_3510495 : Nat := 4983230072969 + 3 ^ 40 * 3510495 * 2
def baseEnd_3510495 : Nat := 600857090068449301956011

theorem tailTrace_3510495 : CollatzResearch.WordTrace tailWord_3510495 prefixEnd_3510495 600857090068449301956011 := by
  unfold tailWord_3510495
  simp only [CollatzResearch.WordTrace]
  refine ⟨128038271417083634658908939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85358847611389089772605959 128038271417083634658908939)
  ·
    refine ⟨192057407125625451988363409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128038271417083634658908939 192057407125625451988363409)
    ·
      refine ⟨144043055344219088991272557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192057407125625451988363409 144043055344219088991272557)
      ·
        refine ⟨54016145754082158371727209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144043055344219088991272557 54016145754082158371727209)
        ·
          refine ⟨40512109315561618778795407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54016145754082158371727209 40512109315561618778795407)
          ·
            refine ⟨60768163973342428168193111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40512109315561618778795407 60768163973342428168193111)
            ·
              refine ⟨91152245960013642252289667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60768163973342428168193111 91152245960013642252289667)
              ·
                refine ⟨136728368940020463378434501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91152245960013642252289667 136728368940020463378434501)
                ·
                  refine ⟨25636569176253836883456469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136728368940020463378434501 25636569176253836883456469)
                  ·
                    refine ⟨600857090068449301956011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25636569176253836883456469 600857090068449301956011)
                    ·
                      rfl

theorem cell23_3510495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_3510495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510495 prefixEnd_3510495 := by exact prefixLift 3510495
  have htrace : WordTrace (prefixWord ++ tailWord_3510495) baseStart_3510495 baseEnd_3510495 := by
    simpa [prefixWord, tailWord_3510495, baseEnd_3510495] using wordTrace_append hprefix tailTrace_3510495
  have hstable : (prefixWord ++ tailWord_3510495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510495).length < 2 ^ (prefixWord ++ tailWord_3510495).sum := by decide
  have hdescent : baseEnd_3510495 < baseStart_3510495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510505 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_3510505 : Nat := 118140960795 + 3510505 * 2 ^ 59
def prefixEnd_3510505 : Nat := 4983230072969 + 3 ^ 40 * 3510505 * 2
def baseEnd_3510505 : Nat := 1802576405011892866742987

theorem tailTrace_3510505 : CollatzResearch.WordTrace tailWord_3510505 prefixEnd_3510505 1802576405011892866742987 := by
  unfold tailWord_3510505
  simp only [CollatzResearch.WordTrace]
  refine ⟨128038636147047406366772969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85359090764698270911181979 128038636147047406366772969)
  ·
    refine ⟨96028977110285554775079727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128038636147047406366772969 96028977110285554775079727)
    ·
      refine ⟨144043465665428332162619591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96028977110285554775079727 144043465665428332162619591)
      ·
        refine ⟨216065198498142498243929387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144043465665428332162619591 216065198498142498243929387)
        ·
          refine ⟨324097797747213747365894081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216065198498142498243929387 324097797747213747365894081)
          ·
            refine ⟨243073348310410310524420561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324097797747213747365894081 243073348310410310524420561)
            ·
              refine ⟨182305011232807732893315421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243073348310410310524420561 182305011232807732893315421)
              ·
                refine ⟨68364379212302899834993283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182305011232807732893315421 68364379212302899834993283)
                ·
                  refine ⟨102546568818454349752489925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68364379212302899834993283 102546568818454349752489925)
                  ·
                    refine ⟨19227481653460190578591861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102546568818454349752489925 19227481653460190578591861)
                    ·
                      refine ⟨1802576405011892866742987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19227481653460190578591861 1802576405011892866742987)
                      ·
                        rfl

theorem cell23_3510505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_3510505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510505 prefixEnd_3510505 := by exact prefixLift 3510505
  have htrace : WordTrace (prefixWord ++ tailWord_3510505) baseStart_3510505 baseEnd_3510505 := by
    simpa [prefixWord, tailWord_3510505, baseEnd_3510505] using wordTrace_append hprefix tailTrace_3510505
  have hstable : (prefixWord ++ tailWord_3510505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510505).length < 2 ^ (prefixWord ++ tailWord_3510505).sum := by decide
  have hdescent : baseEnd_3510505 < baseStart_3510505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510526 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3510526 : Nat := 118140960795 + 3510526 * 2 ^ 59
def prefixEnd_3510526 : Nat := 4983230072969 + 3 ^ 40 * 3510526 * 2
def baseEnd_3510526 : Nat := 1802587188105637284580391

theorem tailTrace_3510526 : CollatzResearch.WordTrace tailWord_3510526 prefixEnd_3510526 1802587188105637284580391 := by
  unfold tailWord_3510526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004925259996415869160929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85359601386647551302191621 16004925259996415869160929)
  ·
    refine ⟨12003693944997311901870697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16004925259996415869160929 12003693944997311901870697)
    ·
      refine ⟨9002770458747983926403023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12003693944997311901870697 9002770458747983926403023)
      ·
        refine ⟨13504155688121975889604535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002770458747983926403023 13504155688121975889604535)
        ·
          refine ⟨20256233532182963834406803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504155688121975889604535 20256233532182963834406803)
          ·
            refine ⟨30384350298274445751610205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256233532182963834406803 30384350298274445751610205)
            ·
              refine ⟨11394131361852917156853827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30384350298274445751610205 11394131361852917156853827)
              ·
                refine ⟨17091197042779375735280741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394131361852917156853827 17091197042779375735280741)
                ·
                  refine ⟨3204599445521132950365139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17091197042779375735280741 3204599445521132950365139)
                  ·
                    refine ⟨4806899168281699425547709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3204599445521132950365139 4806899168281699425547709)
                    ·
                      refine ⟨1802587188105637284580391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4806899168281699425547709 1802587188105637284580391)
                      ·
                        rfl

theorem cell23_3510526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3510526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510526 prefixEnd_3510526 := by exact prefixLift 3510526
  have htrace : WordTrace (prefixWord ++ tailWord_3510526) baseStart_3510526 baseEnd_3510526 := by
    simpa [prefixWord, tailWord_3510526, baseEnd_3510526] using wordTrace_append hprefix tailTrace_3510526
  have hstable : (prefixWord ++ tailWord_3510526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510526).length < 2 ^ (prefixWord ++ tailWord_3510526).sum := by decide
  have hdescent : baseEnd_3510526 < baseStart_3510526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510542 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3510542 : Nat := 118140960795 + 3510542 * 2 ^ 59
def prefixEnd_3510542 : Nat := 4983230072969 + 3 ^ 40 * 3510542 * 2
def baseEnd_3510542 : Nat := 600865134598703073993439

theorem tailTrace_3510542 : CollatzResearch.WordTrace tailWord_3510542 prefixEnd_3510542 600865134598703073993439 := by
  unfold tailWord_3510542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004998205989170210733735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85359990431942241123913253 16004998205989170210733735)
  ·
    refine ⟨24007497308983755316100603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16004998205989170210733735 24007497308983755316100603)
    ·
      refine ⟨36011245963475632974150905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24007497308983755316100603 36011245963475632974150905)
      ·
        refine ⟨27008434472606724730613179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36011245963475632974150905 27008434472606724730613179)
        ·
          refine ⟨40512651708910087095919769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27008434472606724730613179 40512651708910087095919769)
          ·
            refine ⟨30384488781682565321939827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40512651708910087095919769 30384488781682565321939827)
            ·
              refine ⟨45576733172523847982909741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30384488781682565321939827 45576733172523847982909741)
              ·
                refine ⟨17091274939696442993591153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45576733172523847982909741 17091274939696442993591153)
                ·
                  refine ⟨12818456204772332245193365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17091274939696442993591153 12818456204772332245193365)
                  ·
                    refine ⟨600865134598703073993439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12818456204772332245193365 600865134598703073993439)
                    ·
                      rfl

theorem cell23_3510542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3510542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510542 prefixEnd_3510542 := by exact prefixLift 3510542
  have htrace : WordTrace (prefixWord ++ tailWord_3510542) baseStart_3510542 baseEnd_3510542 := by
    simpa [prefixWord, tailWord_3510542, baseEnd_3510542] using wordTrace_append hprefix tailTrace_3510542
  have hstable : (prefixWord ++ tailWord_3510542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510542).length < 2 ^ (prefixWord ++ tailWord_3510542).sum := by decide
  have hdescent : baseEnd_3510542 < baseStart_3510542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510552 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3510552 : Nat := 118140960795 + 3510552 * 2 ^ 59
def prefixEnd_3510552 : Nat := 4983230072969 + 3 ^ 40 * 3510552 * 2
def baseEnd_3510552 : Nat := 1802600538602654182855271

theorem tailTrace_3510552 : CollatzResearch.WordTrace tailWord_3510552 prefixEnd_3510552 1802600538602654182855271 := by
  unfold tailWord_3510552
  simp only [CollatzResearch.WordTrace]
  refine ⟨64020175188938566696866955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85360233585251422262489273 64020175188938566696866955)
  ·
    refine ⟨96030262783407850045300433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64020175188938566696866955 96030262783407850045300433)
    ·
      refine ⟨72022697087555887533975325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96030262783407850045300433 72022697087555887533975325)
      ·
        refine ⟨27008511407833457825240747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72022697087555887533975325 27008511407833457825240747)
        ·
          refine ⟨40512767111750186737861121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27008511407833457825240747 40512767111750186737861121)
          ·
            refine ⟨30384575333812640053395841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40512767111750186737861121 30384575333812640053395841)
            ·
              refine ⟨22788431500359480040046881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30384575333812640053395841 22788431500359480040046881)
              ·
                refine ⟨17091323625269610030035161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22788431500359480040046881 17091323625269610030035161)
                ·
                  refine ⟨12818492718952207522526371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17091323625269610030035161 12818492718952207522526371)
                  ·
                    refine ⟨19227739078428311283789557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12818492718952207522526371 19227739078428311283789557)
                    ·
                      refine ⟨1802600538602654182855271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19227739078428311283789557 1802600538602654182855271)
                      ·
                        rfl

theorem cell23_3510552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3510552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510552 prefixEnd_3510552 := by exact prefixLift 3510552
  have htrace : WordTrace (prefixWord ++ tailWord_3510552) baseStart_3510552 baseEnd_3510552 := by
    simpa [prefixWord, tailWord_3510552, baseEnd_3510552] using wordTrace_append hprefix tailTrace_3510552
  have hstable : (prefixWord ++ tailWord_3510552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510552).length < 2 ^ (prefixWord ++ tailWord_3510552).sum := by decide
  have hdescent : baseEnd_3510552 < baseStart_3510552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510649 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_3510649 : Nat := 118140960795 + 3510649 * 2 ^ 59
def prefixEnd_3510649 : Nat := 4983230072969 + 3 ^ 40 * 3510649 * 2
def baseEnd_3510649 : Nat := 600883448742046767780775

theorem tailTrace_3510649 : CollatzResearch.WordTrace tailWord_3510649 prefixEnd_3510649 600883448742046767780775 := by
  unfold tailWord_3510649
  simp only [CollatzResearch.WordTrace]
  refine ⟨128043888258525718960015001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85362592172350479306676667 128043888258525718960015001)
  ·
    refine ⟨96032916193894289220011251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128043888258525718960015001 96032916193894289220011251)
    ·
      refine ⟨144049374290841433830016877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96032916193894289220011251 144049374290841433830016877)
      ·
        refine ⟨54018515359065537686256329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144049374290841433830016877 54018515359065537686256329)
        ·
          refine ⟨40513886519299153264692247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54018515359065537686256329 40513886519299153264692247)
          ·
            refine ⟨60770829778948729897038371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40513886519299153264692247 60770829778948729897038371)
            ·
              refine ⟨91156244668423094845557557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60770829778948729897038371 91156244668423094845557557)
              ·
                refine ⟨8545897937664665141771021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91156244668423094845557557 8545897937664665141771021)
                ·
                  refine ⟨3204711726624249428164133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8545897937664665141771021 3204711726624249428164133)
                  ·
                    refine ⟨600883448742046767780775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204711726624249428164133 600883448742046767780775)
                    ·
                      rfl

theorem cell23_3510649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_3510649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510649 prefixEnd_3510649 := by exact prefixLift 3510649
  have htrace : WordTrace (prefixWord ++ tailWord_3510649) baseStart_3510649 baseEnd_3510649 := by
    simpa [prefixWord, tailWord_3510649, baseEnd_3510649] using wordTrace_append hprefix tailTrace_3510649
  have hstable : (prefixWord ++ tailWord_3510649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510649).length < 2 ^ (prefixWord ++ tailWord_3510649).sum := by decide
  have hdescent : baseEnd_3510649 < baseStart_3510649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510652 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3510652 : Nat := 118140960795 + 3510652 * 2 ^ 59
def prefixEnd_3510652 : Nat := 4983230072969 + 3 ^ 40 * 3510652 * 2
def baseEnd_3510652 : Nat := 1802651886668103791604811

theorem tailTrace_3510652 : CollatzResearch.WordTrace tailWord_3510652 prefixEnd_3510652 1802651886668103791604811 := by
  unfold tailWord_3510652
  simp only [CollatzResearch.WordTrace]
  refine ⟨64021998838757425236187105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85362665118343233648249473 64021998838757425236187105)
  ·
    refine ⟨48016499129068068927140329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64021998838757425236187105 48016499129068068927140329)
    ·
      refine ⟨36012374346801051695355247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48016499129068068927140329 36012374346801051695355247)
      ·
        refine ⟨54018561520201577543032871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36012374346801051695355247 54018561520201577543032871)
        ·
          refine ⟨81027842280302366314549307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54018561520201577543032871 81027842280302366314549307)
          ·
            refine ⟨121541763420453549471823961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81027842280302366314549307 121541763420453549471823961)
            ·
              refine ⟨91156322565340162103867971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121541763420453549471823961 91156322565340162103867971)
              ·
                refine ⟨136734483848010243155801957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91156322565340162103867971 136734483848010243155801957)
                ·
                  refine ⟨25637715721501920591712867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136734483848010243155801957 25637715721501920591712867)
                  ·
                    refine ⟨38456573582252880887569301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25637715721501920591712867 38456573582252880887569301)
                    ·
                      refine ⟨1802651886668103791604811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38456573582252880887569301 1802651886668103791604811)
                      ·
                        rfl

theorem cell23_3510652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3510652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510652 prefixEnd_3510652 := by exact prefixLift 3510652
  have htrace : WordTrace (prefixWord ++ tailWord_3510652) baseStart_3510652 baseEnd_3510652 := by
    simpa [prefixWord, tailWord_3510652, baseEnd_3510652] using wordTrace_append hprefix tailTrace_3510652
  have hstable : (prefixWord ++ tailWord_3510652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510652).length < 2 ^ (prefixWord ++ tailWord_3510652).sum := by decide
  have hdescent : baseEnd_3510652 < baseStart_3510652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510686 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3510686 : Nat := 118140960795 + 3510686 * 2 ^ 59
def prefixEnd_3510686 : Nat := 4983230072969 + 3 ^ 40 * 3510686 * 2
def baseEnd_3510686 : Nat := 1802669345010356658579655

theorem tailTrace_3510686 : CollatzResearch.WordTrace tailWord_3510686 prefixEnd_3510686 1802669345010356658579655 := by
  unfold tailWord_3510686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005654719923959284888989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85363491839594449519407941 16005654719923959284888989)
  ·
    refine ⟨6002120519971484731833371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16005654719923959284888989 6002120519971484731833371)
    ·
      refine ⟨9003180779957227097750057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6002120519971484731833371 9003180779957227097750057)
      ·
        refine ⟨6752385584967920323312543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9003180779957227097750057 6752385584967920323312543)
        ·
          refine ⟨10128578377451880484968815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752385584967920323312543 10128578377451880484968815)
          ·
            refine ⟨15192867566177820727453223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128578377451880484968815 15192867566177820727453223)
            ·
              refine ⟨22789301349266731091179835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15192867566177820727453223 22789301349266731091179835)
              ·
                refine ⟨34183952023900096636769753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789301349266731091179835 34183952023900096636769753)
                ·
                  refine ⟨25637964017925072477577315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34183952023900096636769753 25637964017925072477577315)
                  ·
                    refine ⟨38456946026887608716365973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25637964017925072477577315 38456946026887608716365973)
                    ·
                      refine ⟨1802669345010356658579655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38456946026887608716365973 1802669345010356658579655)
                      ·
                        rfl

theorem cell23_3510686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3510686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510686 prefixEnd_3510686 := by exact prefixLift 3510686
  have htrace : WordTrace (prefixWord ++ tailWord_3510686) baseStart_3510686 baseEnd_3510686 := by
    simpa [prefixWord, tailWord_3510686, baseEnd_3510686] using wordTrace_append hprefix tailTrace_3510686
  have hstable : (prefixWord ++ tailWord_3510686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510686).length < 2 ^ (prefixWord ++ tailWord_3510686).sum := by decide
  have hdescent : baseEnd_3510686 < baseStart_3510686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510696 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 8]
def baseStart_3510696 : Nat := 118140960795 + 3510696 * 2 ^ 59
def prefixEnd_3510696 : Nat := 4983230072969 + 3 ^ 40 * 3510696 * 2
def baseEnd_3510696 : Nat := 200297164424100179939401

theorem tailTrace_3510696 : CollatzResearch.WordTrace tailWord_3510696 prefixEnd_3510696 200297164424100179939401 := by
  unfold tailWord_3510696
  simp only [CollatzResearch.WordTrace]
  refine ⟨64022801244677722993487971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85363734992903630657983961 64022801244677722993487971)
  ·
    refine ⟨96034201867016584490231957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64022801244677722993487971 96034201867016584490231957)
    ·
      refine ⟨4501603212516402397979623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96034201867016584490231957 4501603212516402397979623)
      ·
        refine ⟨6752404818774603596969435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501603212516402397979623 6752404818774603596969435)
        ·
          refine ⟨10128607228161905395454153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752404818774603596969435 10128607228161905395454153)
          ·
            refine ⟨7596455421121429046590615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128607228161905395454153 7596455421121429046590615)
            ·
              refine ⟨11394683131682143569885923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596455421121429046590615 11394683131682143569885923)
              ·
                refine ⟨17092024697523215354828885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394683131682143569885923 17092024697523215354828885)
                ·
                  refine ⟨200297164424100179939401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17092024697523215354828885 200297164424100179939401)
                  ·
                    rfl

theorem cell23_3510696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_3510696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510696 prefixEnd_3510696 := by exact prefixLift 3510696
  have htrace : WordTrace (prefixWord ++ tailWord_3510696) baseStart_3510696 baseEnd_3510696 := by
    simpa [prefixWord, tailWord_3510696, baseEnd_3510696] using wordTrace_append hprefix tailTrace_3510696
  have hstable : (prefixWord ++ tailWord_3510696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510696).length < 2 ^ (prefixWord ++ tailWord_3510696).sum := by decide
  have hdescent : baseEnd_3510696 < baseStart_3510696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510729 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_3510729 : Nat := 118140960795 + 3510729 * 2 ^ 59
def prefixEnd_3510729 : Nat := 4983230072969 + 3 ^ 40 * 3510729 * 2
def baseEnd_3510729 : Nat := 1802691424678499990341957

theorem tailTrace_3510729 : CollatzResearch.WordTrace tailWord_3510729 prefixEnd_3510729 1802691424678499990341957 := by
  unfold tailWord_3510729
  simp only [CollatzResearch.WordTrace]
  refine ⟨128046806098235892622927241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85364537398823928415284827 128046806098235892622927241)
  ·
    refine ⟨96035104573676919467195431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128046806098235892622927241 96035104573676919467195431)
    ·
      refine ⟨144052656860515379200793147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96035104573676919467195431 144052656860515379200793147)
      ·
        refine ⟨216078985290773068801189721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144052656860515379200793147 216078985290773068801189721)
        ·
          refine ⟨162059238968079801600892291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216078985290773068801189721 162059238968079801600892291)
          ·
            refine ⟨243088858452119702401338437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162059238968079801600892291 243088858452119702401338437)
            ·
              refine ⟨45579160959772444200250957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243088858452119702401338437 45579160959772444200250957)
              ·
                refine ⟨17092185359914666575094109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45579160959772444200250957 17092185359914666575094109)
                ·
                  refine ⟨6409569509967999965660291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17092185359914666575094109 6409569509967999965660291)
                  ·
                    refine ⟨9614354264951999948490437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409569509967999965660291 9614354264951999948490437)
                    ·
                      refine ⟨1802691424678499990341957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9614354264951999948490437 1802691424678499990341957)
                      ·
                        rfl

theorem cell23_3510729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_3510729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510729 prefixEnd_3510729 := by exact prefixLift 3510729
  have htrace : WordTrace (prefixWord ++ tailWord_3510729) baseStart_3510729 baseEnd_3510729 := by
    simpa [prefixWord, tailWord_3510729, baseEnd_3510729] using wordTrace_append hprefix tailTrace_3510729
  have hstable : (prefixWord ++ tailWord_3510729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510729).length < 2 ^ (prefixWord ++ tailWord_3510729).sum := by decide
  have hdescent : baseEnd_3510729 < baseStart_3510729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510746 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_3510746 : Nat := 118140960795 + 3510746 * 2 ^ 59
def prefixEnd_3510746 : Nat := 4983230072969 + 3 ^ 40 * 3510746 * 2
def baseEnd_3510746 : Nat := 1802700153849626423829379

theorem tailTrace_3510746 : CollatzResearch.WordTrace tailWord_3510746 prefixEnd_3510746 1802700153849626423829379 := by
  unfold tailWord_3510746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011856534793576131574023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85364950759449536350864061 32011856534793576131574023)
  ·
    refine ⟨48017784802190364197361035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011856534793576131574023 48017784802190364197361035)
    ·
      refine ⟨72026677203285546296041553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48017784802190364197361035 72026677203285546296041553)
      ·
        refine ⟨54020007902464159722031165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72026677203285546296041553 54020007902464159722031165)
        ·
          refine ⟨20257502963424059895761687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54020007902464159722031165 20257502963424059895761687)
          ·
            refine ⟨30386254445136089843642531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20257502963424059895761687 30386254445136089843642531)
            ·
              refine ⟨45579381667704134765463797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30386254445136089843642531 45579381667704134765463797)
              ·
                refine ⟨4273067031347262634262231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45579381667704134765463797 4273067031347262634262231)
                ·
                  refine ⟨6409600547020893951393347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273067031347262634262231 6409600547020893951393347)
                  ·
                    refine ⟨9614400820531340927090021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409600547020893951393347 9614400820531340927090021)
                    ·
                      refine ⟨1802700153849626423829379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9614400820531340927090021 1802700153849626423829379)
                      ·
                        rfl

theorem cell23_3510746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_3510746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510746 prefixEnd_3510746 := by exact prefixLift 3510746
  have htrace : WordTrace (prefixWord ++ tailWord_3510746) baseStart_3510746 baseEnd_3510746 := by
    simpa [prefixWord, tailWord_3510746, baseEnd_3510746] using wordTrace_append hprefix tailTrace_3510746
  have hstable : (prefixWord ++ tailWord_3510746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510746).length < 2 ^ (prefixWord ++ tailWord_3510746).sum := by decide
  have hdescent : baseEnd_3510746 < baseStart_3510746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510757 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3510757 : Nat := 118140960795 + 3510757 * 2 ^ 59
def prefixEnd_3510757 : Nat := 4983230072969 + 3 ^ 40 * 3510757 * 2
def baseEnd_3510757 : Nat := 1802705802136825880791829

theorem tailTrace_3510757 : CollatzResearch.WordTrace tailWord_3510757 prefixEnd_3510757 1802705802136825880791829 := by
  unfold tailWord_3510757
  simp only [CollatzResearch.WordTrace]
  refine ⟨128047827342134453404946525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85365218228089635603297683 128047827342134453404946525)
  ·
    refine ⟨48017935253300420026854947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128047827342134453404946525 48017935253300420026854947)
    ·
      refine ⟨72026902879950630040282421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48017935253300420026854947 72026902879950630040282421)
      ·
        refine ⟨6752522144995371566276477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72026902879950630040282421 6752522144995371566276477)
        ·
          refine ⟨2532195804373264337353679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6752522144995371566276477 2532195804373264337353679)
          ·
            refine ⟨3798293706559896506030519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532195804373264337353679 3798293706559896506030519)
            ·
              refine ⟨5697440559839844759045779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798293706559896506030519 5697440559839844759045779)
              ·
                refine ⟨8546160839759767138568669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697440559839844759045779 8546160839759767138568669)
                ·
                  refine ⟨3204810314909912676963251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8546160839759767138568669 3204810314909912676963251)
                  ·
                    refine ⟨4807215472364869015444877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3204810314909912676963251 4807215472364869015444877)
                    ·
                      refine ⟨1802705802136825880791829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4807215472364869015444877 1802705802136825880791829)
                      ·
                        rfl

theorem cell23_3510757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3510757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510757 prefixEnd_3510757 := by exact prefixLift 3510757
  have htrace : WordTrace (prefixWord ++ tailWord_3510757) baseStart_3510757 baseEnd_3510757 := by
    simpa [prefixWord, tailWord_3510757, baseEnd_3510757] using wordTrace_append hprefix tailTrace_3510757
  have hstable : (prefixWord ++ tailWord_3510757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510757).length < 2 ^ (prefixWord ++ tailWord_3510757).sum := by decide
  have hdescent : baseEnd_3510757 < baseStart_3510757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510759 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3510759 : Nat := 118140960795 + 3510759 * 2 ^ 59
def prefixEnd_3510759 : Nat := 4983230072969 + 3 ^ 40 * 3510759 * 2
def baseEnd_3510759 : Nat := 1802706829098134872966819

theorem tailTrace_3510759 : CollatzResearch.WordTrace tailWord_3510759 prefixEnd_3510759 1802706829098134872966819 := by
  unfold tailWord_3510759
  simp only [CollatzResearch.WordTrace]
  refine ⟨128047900288127207746519331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85365266858751471831012887 128047900288127207746519331)
  ·
    refine ⟨192071850432190811619778997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128047900288127207746519331 192071850432190811619778997)
    ·
      refine ⟨18006735978017888589354281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192071850432190811619778997 18006735978017888589354281)
      ·
        refine ⟨13505051983513416442015711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18006735978017888589354281 13505051983513416442015711)
        ·
          refine ⟨20257577975270124663023567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13505051983513416442015711 20257577975270124663023567)
          ·
            refine ⟨30386366962905186994535351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20257577975270124663023567 30386366962905186994535351)
            ·
              refine ⟨45579550444357780491803027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30386366962905186994535351 45579550444357780491803027)
              ·
                refine ⟨68369325666536670737704541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45579550444357780491803027 68369325666536670737704541)
                ·
                  refine ⟨25638497124951251526639203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68369325666536670737704541 25638497124951251526639203)
                  ·
                    refine ⟨38457745687426877289958805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25638497124951251526639203 38457745687426877289958805)
                    ·
                      refine ⟨1802706829098134872966819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38457745687426877289958805 1802706829098134872966819)
                      ·
                        rfl

theorem cell23_3510759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3510759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510759 prefixEnd_3510759 := by exact prefixLift 3510759
  have htrace : WordTrace (prefixWord ++ tailWord_3510759) baseStart_3510759 baseEnd_3510759 := by
    simpa [prefixWord, tailWord_3510759, baseEnd_3510759] using wordTrace_append hprefix tailTrace_3510759
  have hstable : (prefixWord ++ tailWord_3510759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510759).length < 2 ^ (prefixWord ++ tailWord_3510759).sum := by decide
  have hdescent : baseEnd_3510759 < baseStart_3510759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510766 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3510766 : Nat := 118140960795 + 3510766 * 2 ^ 59
def prefixEnd_3510766 : Nat := 4983230072969 + 3 ^ 40 * 3510766 * 2
def baseEnd_3510766 : Nat := 1802710423462716345579287

theorem tailTrace_3510766 : CollatzResearch.WordTrace tailWord_3510766 prefixEnd_3510766 1802710423462716345579287 := by
  unfold tailWord_3510766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006019449887730992753019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85365437066067898628016101 16006019449887730992753019)
  ·
    refine ⟨24009029174831596489129529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16006019449887730992753019 24009029174831596489129529)
    ·
      refine ⟨18006771881123697366847147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24009029174831596489129529 18006771881123697366847147)
      ·
        refine ⟨27010157821685546050270721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18006771881123697366847147 27010157821685546050270721)
        ·
          refine ⟨20257618366264159537703041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27010157821685546050270721 20257618366264159537703041)
          ·
            refine ⟨15193213774698119653277281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20257618366264159537703041 15193213774698119653277281)
            ·
              refine ⟨11394910331023589739957961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15193213774698119653277281 11394910331023589739957961)
              ·
                refine ⟨8546182748267692304968471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394910331023589739957961 8546182748267692304968471)
                ·
                  refine ⟨12819274122401538457452707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546182748267692304968471 12819274122401538457452707)
                  ·
                    refine ⟨19228911183602307686179061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12819274122401538457452707 19228911183602307686179061)
                    ·
                      refine ⟨1802710423462716345579287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19228911183602307686179061 1802710423462716345579287)
                      ·
                        rfl

theorem cell23_3510766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3510766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510766 prefixEnd_3510766 := by exact prefixLift 3510766
  have htrace : WordTrace (prefixWord ++ tailWord_3510766) baseStart_3510766 baseEnd_3510766 := by
    simpa [prefixWord, tailWord_3510766, baseEnd_3510766] using wordTrace_append hprefix tailTrace_3510766
  have hstable : (prefixWord ++ tailWord_3510766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510766).length < 2 ^ (prefixWord ++ tailWord_3510766).sum := by decide
  have hdescent : baseEnd_3510766 < baseStart_3510766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510769 : List Nat := [1, 2, 2, 2, 3, 1, 4, 8]
def baseStart_3510769 : Nat := 118140960795 + 3510769 * 2 ^ 59
def prefixEnd_3510769 : Nat := 4983230072969 + 3 ^ 40 * 3510769 * 2
def baseEnd_3510769 : Nat := 66767109774247401253399

theorem tailTrace_3510769 : CollatzResearch.WordTrace tailWord_3510769 prefixEnd_3510769 66767109774247401253399 := by
  unfold tailWord_3510769
  simp only [CollatzResearch.WordTrace]
  refine ⟨128048265018090979454383361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85365510012060652969588907 128048265018090979454383361)
  ·
    refine ⟨96036198763568234590787521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128048265018090979454383361 96036198763568234590787521)
    ·
      refine ⟨72027149072676175943090641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96036198763568234590787521 72027149072676175943090641)
      ·
        refine ⟨54020361804507131957317981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72027149072676175943090641 54020361804507131957317981)
        ·
          refine ⟨20257635676690174483994243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54020361804507131957317981 20257635676690174483994243)
          ·
            refine ⟨30386453515035261725991365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20257635676690174483994243 30386453515035261725991365)
            ·
              refine ⟨5697460034069111573623381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30386453515035261725991365 5697460034069111573623381)
              ·
                refine ⟨66767109774247401253399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5697460034069111573623381 66767109774247401253399)
                ·
                  rfl

theorem cell23_3510769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 8].length) (baseStart_3510769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510769 prefixEnd_3510769 := by exact prefixLift 3510769
  have htrace : WordTrace (prefixWord ++ tailWord_3510769) baseStart_3510769 baseEnd_3510769 := by
    simpa [prefixWord, tailWord_3510769, baseEnd_3510769] using wordTrace_append hprefix tailTrace_3510769
  have hstable : (prefixWord ++ tailWord_3510769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510769).length < 2 ^ (prefixWord ++ tailWord_3510769).sum := by decide
  have hdescent : baseEnd_3510769 < baseStart_3510769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510790 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3510790 : Nat := 118140960795 + 3510790 * 2 ^ 59
def prefixEnd_3510790 : Nat := 4983230072969 + 3 ^ 40 * 3510790 * 2
def baseEnd_3510790 : Nat := 600907582332808083893059

theorem tailTrace_3510790 : CollatzResearch.WordTrace tailWord_3510790 prefixEnd_3510790 600907582332808083893059 := by
  unfold tailWord_3510790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001532217219215626278057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85366020634009933360598549 4001532217219215626278057)
  ·
    refine ⟨3001149162914411719708543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4001532217219215626278057 3001149162914411719708543)
    ·
      refine ⟨4501723744371617579562815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001149162914411719708543 4501723744371617579562815)
      ·
        refine ⟨6752585616557426369344223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501723744371617579562815 6752585616557426369344223)
        ·
          refine ⟨10128878424836139554016335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752585616557426369344223 10128878424836139554016335)
          ·
            refine ⟨15193317637254209331024503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128878424836139554016335 15193317637254209331024503)
            ·
              refine ⟨22789976455881313996536755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15193317637254209331024503 22789976455881313996536755)
              ·
                refine ⟨34184964683821970994805133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789976455881313996536755 34184964683821970994805133)
                ·
                  refine ⟨12819361756433239123051925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34184964683821970994805133 12819361756433239123051925)
                  ·
                    refine ⟨600907582332808083893059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12819361756433239123051925 600907582332808083893059)
                    ·
                      rfl

theorem cell23_3510790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3510790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510790 prefixEnd_3510790 := by exact prefixLift 3510790
  have htrace : WordTrace (prefixWord ++ tailWord_3510790) baseStart_3510790 baseEnd_3510790 := by
    simpa [prefixWord, tailWord_3510790, baseEnd_3510790] using wordTrace_append hprefix tailTrace_3510790
  have hstable : (prefixWord ++ tailWord_3510790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510790).length < 2 ^ (prefixWord ++ tailWord_3510790).sum := by decide
  have hdescent : baseEnd_3510790 < baseStart_3510790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510796 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3510796 : Nat := 118140960795 + 3510796 * 2 ^ 59
def prefixEnd_3510796 : Nat := 4983230072969 + 3 ^ 40 * 3510796 * 2
def baseEnd_3510796 : Nat := 1802725827882351228204149

theorem tailTrace_3510796 : CollatzResearch.WordTrace tailWord_3510796 prefixEnd_3510796 1802725827882351228204149 := by
  unfold tailWord_3510796
  simp only [CollatzResearch.WordTrace]
  refine ⟨64024624894496581532808121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85366166525995442043744161 64024624894496581532808121)
  ·
    refine ⟨48018468670872436149606091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64024624894496581532808121 48018468670872436149606091)
    ·
      refine ⟨72027703006308654224409137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48018468670872436149606091 72027703006308654224409137)
      ·
        refine ⟨54020777254731490668306853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72027703006308654224409137 54020777254731490668306853)
        ·
          refine ⟨10128895735262154500307535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54020777254731490668306853 10128895735262154500307535)
          ·
            refine ⟨15193343602893231750461303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128895735262154500307535 15193343602893231750461303)
            ·
              refine ⟨22790015404339847625691955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15193343602893231750461303 22790015404339847625691955)
              ·
                refine ⟨34185023106509771438537933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22790015404339847625691955 34185023106509771438537933)
                ·
                  refine ⟨12819383664941164289451725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34185023106509771438537933 12819383664941164289451725)
                  ·
                    refine ⟨4807268874352936608544397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12819383664941164289451725 4807268874352936608544397)
                    ·
                      refine ⟨1802725827882351228204149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4807268874352936608544397 1802725827882351228204149)
                      ·
                        rfl

theorem cell23_3510796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3510796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510796 prefixEnd_3510796 := by exact prefixLift 3510796
  have htrace : WordTrace (prefixWord ++ tailWord_3510796) baseStart_3510796 baseEnd_3510796 := by
    simpa [prefixWord, tailWord_3510796, baseEnd_3510796] using wordTrace_append hprefix tailTrace_3510796
  have hstable : (prefixWord ++ tailWord_3510796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510796).length < 2 ^ (prefixWord ++ tailWord_3510796).sum := by decide
  have hdescent : baseEnd_3510796 < baseStart_3510796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510820 : List Nat := [2, 3, 1, 5, 2, 1, 1, 8]
def baseStart_3510820 : Nat := 118140960795 + 3510820 * 2 ^ 59
def prefixEnd_3510820 : Nat := 4983230072969 + 3 ^ 40 * 3510820 * 2
def baseEnd_3510820 : Nat := 66768079682150338307557

theorem tailTrace_3510820 : CollatzResearch.WordTrace tailWord_3510820 prefixEnd_3510820 66768079682150338307557 := by
  unfold tailWord_3510820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64025062570453107582244957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85366750093937476776326609 64025062570453107582244957)
  ·
    refine ⟨24009398463919915343341859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64025062570453107582244957 24009398463919915343341859)
    ·
      refine ⟨36014097695879873015012789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24009398463919915343341859 36014097695879873015012789)
      ·
        refine ⟨3376321658988738095157449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36014097695879873015012789 3376321658988738095157449)
        ·
          refine ⟨2532241244241553571368087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376321658988738095157449 2532241244241553571368087)
          ·
            refine ⟨3798361866362330357052131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532241244241553571368087 3798361866362330357052131)
            ·
              refine ⟨5697542799543495535578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798361866362330357052131 5697542799543495535578197)
              ·
                refine ⟨66768079682150338307557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5697542799543495535578197 66768079682150338307557)
                ·
                  rfl

theorem cell23_3510820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 8].length) (baseStart_3510820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510820 prefixEnd_3510820 := by exact prefixLift 3510820
  have htrace : WordTrace (prefixWord ++ tailWord_3510820) baseStart_3510820 baseEnd_3510820 := by
    simpa [prefixWord, tailWord_3510820, baseEnd_3510820] using wordTrace_append hprefix tailTrace_3510820
  have hstable : (prefixWord ++ tailWord_3510820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510820).length < 2 ^ (prefixWord ++ tailWord_3510820).sum := by decide
  have hdescent : baseEnd_3510820 < baseStart_3510820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510830 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3510830 : Nat := 118140960795 + 3510830 * 2 ^ 59
def prefixEnd_3510830 : Nat := 4983230072969 + 3 ^ 40 * 3510830 * 2
def baseEnd_3510830 : Nat := 1802743286224604095178993

theorem tailTrace_3510830 : CollatzResearch.WordTrace tailWord_3510830 prefixEnd_3510830 1802743286224604095178993 := by
  unfold tailWord_3510830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006311233858748359044243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85366993247246657914902629 16006311233858748359044243)
  ·
    refine ⟨24009466850788122538566365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16006311233858748359044243 24009466850788122538566365)
    ·
      refine ⟨9003550069045545951962387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24009466850788122538566365 9003550069045545951962387)
      ·
        refine ⟨13505325103568318927943581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003550069045545951962387 13505325103568318927943581)
        ·
          refine ⟨5064496913838119597978843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13505325103568318927943581 5064496913838119597978843)
          ·
            refine ⟨7596745370757179396968265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064496913838119597978843 7596745370757179396968265)
            ·
              refine ⟨5697559028067884547726199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596745370757179396968265 5697559028067884547726199)
              ·
                refine ⟨8546338542101826821589299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697559028067884547726199 8546338542101826821589299)
                ·
                  refine ⟨12819507813152740232383949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546338542101826821589299 12819507813152740232383949)
                  ·
                    refine ⟨4807315429932277587143981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12819507813152740232383949 4807315429932277587143981)
                    ·
                      refine ⟨1802743286224604095178993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4807315429932277587143981 1802743286224604095178993)
                      ·
                        rfl

theorem cell23_3510830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3510830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510830 prefixEnd_3510830 := by exact prefixLift 3510830
  have htrace : WordTrace (prefixWord ++ tailWord_3510830) baseStart_3510830 baseEnd_3510830 := by
    simpa [prefixWord, tailWord_3510830, baseEnd_3510830] using wordTrace_append hprefix tailTrace_3510830
  have hstable : (prefixWord ++ tailWord_3510830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510830).length < 2 ^ (prefixWord ++ tailWord_3510830).sum := by decide
  have hdescent : baseEnd_3510830 < baseStart_3510830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510853 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_3510853 : Nat := 118140960795 + 3510853 * 2 ^ 59
def prefixEnd_3510853 : Nat := 4983230072969 + 3 ^ 40 * 3510853 * 2
def baseEnd_3510853 : Nat := 1802755096279657505191387

theorem tailTrace_3510853 : CollatzResearch.WordTrace tailWord_3510853 prefixEnd_3510853 1802755096279657505191387 := by
  unfold tailWord_3510853
  simp only [CollatzResearch.WordTrace]
  refine ⟨128051328749786661800441213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85367552499857774533627475 128051328749786661800441213)
  ·
    refine ⟨48019248281169998175165455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128051328749786661800441213 48019248281169998175165455)
    ·
      refine ⟨72028872421754997262748183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48019248281169998175165455 72028872421754997262748183)
      ·
        refine ⟨108043308632632495894122275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72028872421754997262748183 108043308632632495894122275)
        ·
          refine ⟨162064962948948743841183413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108043308632632495894122275 162064962948948743841183413)
          ·
            refine ⟨15193590276463944735110945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162064962948948743841183413 15193590276463944735110945)
            ·
              refine ⟨11395192707347958551333209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15193590276463944735110945 11395192707347958551333209)
              ·
                refine ⟨8546394530510968913499907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11395192707347958551333209 8546394530510968913499907)
                ·
                  refine ⟨12819591795766453370249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546394530510968913499907 12819591795766453370249861)
                  ·
                    refine ⟨2403673461706210006921849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12819591795766453370249861 2403673461706210006921849)
                    ·
                      refine ⟨1802755096279657505191387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403673461706210006921849 1802755096279657505191387)
                      ·
                        rfl

theorem cell23_3510853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_3510853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510853 prefixEnd_3510853 := by exact prefixLift 3510853
  have htrace : WordTrace (prefixWord ++ tailWord_3510853) baseStart_3510853 baseEnd_3510853 := by
    simpa [prefixWord, tailWord_3510853, baseEnd_3510853] using wordTrace_append hprefix tailTrace_3510853
  have hstable : (prefixWord ++ tailWord_3510853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510853).length < 2 ^ (prefixWord ++ tailWord_3510853).sum := by decide
  have hdescent : baseEnd_3510853 < baseStart_3510853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510866 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3510866 : Nat := 118140960795 + 3510866 * 2 ^ 59
def prefixEnd_3510866 : Nat := 4983230072969 + 3 ^ 40 * 3510866 * 2
def baseEnd_3510866 : Nat := 1802761771528165954328827

theorem tailTrace_3510866 : CollatzResearch.WordTrace tailWord_3510866 prefixEnd_3510866 1802761771528165954328827 := by
  unfold tailWord_3510866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32012950724684891255166113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85367868599159710013776301 32012950724684891255166113)
  ·
    refine ⟨24009713043513668441374585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32012950724684891255166113 24009713043513668441374585)
    ·
      refine ⟨18007284782635251331030939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24009713043513668441374585 18007284782635251331030939)
      ·
        refine ⟨27010927173952876996546409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18007284782635251331030939 27010927173952876996546409)
        ·
          refine ⟨20258195380464657747409807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27010927173952876996546409 20258195380464657747409807)
          ·
            refine ⟨30387293070696986621114711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20258195380464657747409807 30387293070696986621114711)
            ·
              refine ⟨45580939606045479931672067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30387293070696986621114711 45580939606045479931672067)
              ·
                refine ⟨68371409409068219897508101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45580939606045479931672067 68371409409068219897508101)
                ·
                  refine ⟨12819639264200291230782769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68371409409068219897508101 12819639264200291230782769)
                  ·
                    refine ⟨9614729448150218423087077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12819639264200291230782769 9614729448150218423087077)
                    ·
                      refine ⟨1802761771528165954328827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9614729448150218423087077 1802761771528165954328827)
                      ·
                        rfl

theorem cell23_3510866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3510866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510866 prefixEnd_3510866 := by exact prefixLift 3510866
  have htrace : WordTrace (prefixWord ++ tailWord_3510866) baseStart_3510866 baseEnd_3510866 := by
    simpa [prefixWord, tailWord_3510866, baseEnd_3510866] using wordTrace_append hprefix tailTrace_3510866
  have hstable : (prefixWord ++ tailWord_3510866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510866).length < 2 ^ (prefixWord ++ tailWord_3510866).sum := by decide
  have hdescent : baseEnd_3510866 < baseStart_3510866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510899 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_3510899 : Nat := 118140960795 + 3510899 * 2 ^ 59
def prefixEnd_3510899 : Nat := 4983230072969 + 3 ^ 40 * 3510899 * 2
def baseEnd_3510899 : Nat := 1802778716389764325216175

theorem tailTrace_3510899 : CollatzResearch.WordTrace tailWord_3510899 prefixEnd_3510899 1802778716389764325216175 := by
  unfold tailWord_3510899
  simp only [CollatzResearch.WordTrace]
  refine ⟨128053006507620011656615751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85368671005080007771077167 128053006507620011656615751)
  ·
    refine ⟨192079509761430017484923627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128053006507620011656615751 192079509761430017484923627)
    ·
      refine ⟨288119264642145026227385441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192079509761430017484923627 288119264642145026227385441)
      ·
        refine ⟨216089448481608769670539081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288119264642145026227385441 216089448481608769670539081)
        ·
          refine ⟨162067086361206577252904311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216089448481608769670539081 162067086361206577252904311)
          ·
            refine ⟨243100629541809865879356467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162067086361206577252904311 243100629541809865879356467)
            ·
              refine ⟨364650944312714798819034701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243100629541809865879356467 364650944312714798819034701)
              ·
                refine ⟨136744104117268049557138013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364650944312714798819034701 136744104117268049557138013)
                ·
                  refine ⟨51279039043975518583926755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136744104117268049557138013 51279039043975518583926755)
                  ·
                    refine ⟨76918558565963277875890133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51279039043975518583926755 76918558565963277875890133)
                    ·
                      refine ⟨1802778716389764325216175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76918558565963277875890133 1802778716389764325216175)
                      ·
                        rfl

theorem cell23_3510899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_3510899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510899 prefixEnd_3510899 := by exact prefixLift 3510899
  have htrace : WordTrace (prefixWord ++ tailWord_3510899) baseStart_3510899 baseEnd_3510899 := by
    simpa [prefixWord, tailWord_3510899, baseEnd_3510899] using wordTrace_append hprefix tailTrace_3510899
  have hstable : (prefixWord ++ tailWord_3510899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510899).length < 2 ^ (prefixWord ++ tailWord_3510899).sum := by decide
  have hdescent : baseEnd_3510899 < baseStart_3510899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510938 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3510938 : Nat := 118140960795 + 3510938 * 2 ^ 59
def prefixEnd_3510938 : Nat := 4983230072969 + 3 ^ 40 * 3510938 * 2
def baseEnd_3510938 : Nat := 1802798742135289672628497

theorem tailTrace_3510938 : CollatzResearch.WordTrace tailWord_3510938 prefixEnd_3510938 1802798742135289672628497 := by
  unfold tailWord_3510938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32013607238619680329321367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85369619302985814211523645 32013607238619680329321367)
  ·
    refine ⟨48020410857929520493982051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32013607238619680329321367 48020410857929520493982051)
    ·
      refine ⟨72030616286894280740973077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48020410857929520493982051 72030616286894280740973077)
      ·
        refine ⟨3376435138448169409733113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72030616286894280740973077 3376435138448169409733113)
        ·
          refine ⟨2532326353836127057299835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376435138448169409733113 2532326353836127057299835)
          ·
            refine ⟨3798489530754190585949753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532326353836127057299835 3798489530754190585949753)
            ·
              refine ⟨2848867148065642939462315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798489530754190585949753 2848867148065642939462315)
              ·
                refine ⟨4273300722098464409193473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848867148065642939462315 4273300722098464409193473)
                ·
                  refine ⟨3204975541573848306895105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273300722098464409193473 3204975541573848306895105)
                  ·
                    refine ⟨2403731656180386230171329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3204975541573848306895105 2403731656180386230171329)
                    ·
                      refine ⟨1802798742135289672628497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403731656180386230171329 1802798742135289672628497)
                      ·
                        rfl

theorem cell23_3510938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3510938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510938 prefixEnd_3510938 := by exact prefixLift 3510938
  have htrace : WordTrace (prefixWord ++ tailWord_3510938) baseStart_3510938 baseEnd_3510938 := by
    simpa [prefixWord, tailWord_3510938, baseEnd_3510938] using wordTrace_append hprefix tailTrace_3510938
  have hstable : (prefixWord ++ tailWord_3510938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510938).length < 2 ^ (prefixWord ++ tailWord_3510938).sum := by decide
  have hdescent : baseEnd_3510938 < baseStart_3510938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510963 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3]
def baseStart_3510963 : Nat := 118140960795 + 3510963 * 2 ^ 59
def prefixEnd_3510963 : Nat := 4983230072969 + 3 ^ 40 * 3510963 * 2
def baseEnd_3510963 : Nat := 1802811579151652074815881

theorem tailTrace_3510963 : CollatzResearch.WordTrace tailWord_3510963 prefixEnd_3510963 1802811579151652074815881 := by
  unfold tailWord_3510963
  simp only [CollatzResearch.WordTrace]
  refine ⟨128055340779388150586945543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85370227186258767057963695 128055340779388150586945543)
  ·
    refine ⟨192083011169082225880418315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128055340779388150586945543 192083011169082225880418315)
    ·
      refine ⟨288124516753623338820627473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192083011169082225880418315 288124516753623338820627473)
      ·
        refine ⟨216093387565217504115470605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288124516753623338820627473 216093387565217504115470605)
        ·
          refine ⟨81035020336956564043301477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216093387565217504115470605 81035020336956564043301477)
          ·
            refine ⟨15194066313179355758119027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81035020336956564043301477 15194066313179355758119027)
            ·
              refine ⟨22791099469769033637178541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15194066313179355758119027 22791099469769033637178541)
              ·
                refine ⟨8546662301163387613941953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22791099469769033637178541 8546662301163387613941953)
                ·
                  refine ⟨6409996725872540710456465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8546662301163387613941953 6409996725872540710456465)
                  ·
                    refine ⟨4807497544404405532842349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6409996725872540710456465 4807497544404405532842349)
                    ·
                      refine ⟨1802811579151652074815881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4807497544404405532842349 1802811579151652074815881)
                      ·
                        rfl

theorem cell23_3510963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_3510963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510963 prefixEnd_3510963 := by exact prefixLift 3510963
  have htrace : WordTrace (prefixWord ++ tailWord_3510963) baseStart_3510963 baseEnd_3510963 := by
    simpa [prefixWord, tailWord_3510963, baseEnd_3510963] using wordTrace_append hprefix tailTrace_3510963
  have hstable : (prefixWord ++ tailWord_3510963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510963).length < 2 ^ (prefixWord ++ tailWord_3510963).sum := by decide
  have hdescent : baseEnd_3510963 < baseStart_3510963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510970 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_3510970 : Nat := 118140960795 + 3510970 * 2 ^ 59
def prefixEnd_3510970 : Nat := 4983230072969 + 3 ^ 40 * 3510970 * 2
def baseEnd_3510970 : Nat := 600938391172077849142783

theorem tailTrace_3510970 : CollatzResearch.WordTrace tailWord_3510970 prefixEnd_3510970 600938391172077849142783 := by
  unfold tailWord_3510970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32013899022590697695612591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85370397393575193854966909 32013899022590697695612591)
  ·
    refine ⟨48020848533886046543418887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32013899022590697695612591 48020848533886046543418887)
    ·
      refine ⟨72031272800829069815128331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48020848533886046543418887 72031272800829069815128331)
      ·
        refine ⟨108046909201243604722692497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72031272800829069815128331 108046909201243604722692497)
        ·
          refine ⟨81035181900932703542019373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108046909201243604722692497 81035181900932703542019373)
          ·
            refine ⟨30388193212849763828257265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81035181900932703542019373 30388193212849763828257265)
            ·
              refine ⟨22791144909637322871192949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30388193212849763828257265 22791144909637322871192949)
              ·
                refine ⟨2136669835278499019174339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22791144909637322871192949 2136669835278499019174339)
                ·
                  refine ⟨3205004752917748528761509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136669835278499019174339 3205004752917748528761509)
                  ·
                    refine ⟨600938391172077849142783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205004752917748528761509 600938391172077849142783)
                    ·
                      rfl

theorem cell23_3510970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_3510970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510970 prefixEnd_3510970 := by exact prefixLift 3510970
  have htrace : WordTrace (prefixWord ++ tailWord_3510970) baseStart_3510970 baseEnd_3510970 := by
    simpa [prefixWord, tailWord_3510970, baseEnd_3510970] using wordTrace_append hprefix tailTrace_3510970
  have hstable : (prefixWord ++ tailWord_3510970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510970).length < 2 ^ (prefixWord ++ tailWord_3510970).sum := by decide
  have hdescent : baseEnd_3510970 < baseStart_3510970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3510980 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3510980 : Nat := 118140960795 + 3510980 * 2 ^ 59
def prefixEnd_3510980 : Nat := 4983230072969 + 3 ^ 40 * 3510980 * 2
def baseEnd_3510980 : Nat := 1802820308322778508303303

theorem tailTrace_3510980 : CollatzResearch.WordTrace tailWord_3510980 prefixEnd_3510980 1802820308322778508303303 := by
  unfold tailWord_3510980
  simp only [CollatzResearch.WordTrace]
  refine ⟨64027980410163281245157197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85370640546884374993542929 64027980410163281245157197)
  ·
    refine ⟨24010492653811230466933949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64027980410163281245157197 24010492653811230466933949)
    ·
      refine ⟨9003934745179211425100231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24010492653811230466933949 9003934745179211425100231)
      ·
        refine ⟨13505902117768817137650347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003934745179211425100231 13505902117768817137650347)
        ·
          refine ⟨20258853176653225706475521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13505902117768817137650347 20258853176653225706475521)
          ·
            refine ⟨15194139882489919279856641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20258853176653225706475521 15194139882489919279856641)
            ·
              refine ⟨11395604911867439459892481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15194139882489919279856641 11395604911867439459892481)
              ·
                refine ⟨8546703683900579594919361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11395604911867439459892481 8546703683900579594919361)
                ·
                  refine ⟨6410027762925434696189521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8546703683900579594919361 6410027762925434696189521)
                  ·
                    refine ⟨4807520822194076022142141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410027762925434696189521 4807520822194076022142141)
                    ·
                      refine ⟨1802820308322778508303303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4807520822194076022142141 1802820308322778508303303)
                      ·
                        rfl

theorem cell23_3510980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3510980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3510980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3510980 prefixEnd_3510980 := by exact prefixLift 3510980
  have htrace : WordTrace (prefixWord ++ tailWord_3510980) baseStart_3510980 baseEnd_3510980 := by
    simpa [prefixWord, tailWord_3510980, baseEnd_3510980] using wordTrace_append hprefix tailTrace_3510980
  have hstable : (prefixWord ++ tailWord_3510980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3510980).length < 2 ^ (prefixWord ++ tailWord_3510980).sum := by decide
  have hdescent : baseEnd_3510980 < baseStart_3510980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3510980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511013 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_3511013 : Nat := 118140960795 + 3511013 * 2 ^ 59
def prefixEnd_3511013 : Nat := 4983230072969 + 3 ^ 40 * 3511013 * 2
def baseEnd_3511013 : Nat := 600945751061458959730217

theorem tailTrace_3511013 : CollatzResearch.WordTrace tailWord_3511013 prefixEnd_3511013 600945751061458959730217 := by
  unfold tailWord_3511013
  simp only [CollatzResearch.WordTrace]
  refine ⟨128057164429207009126265693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85371442952804672750843795 128057164429207009126265693)
  ·
    refine ⟨48021436660952628422349635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128057164429207009126265693 48021436660952628422349635)
    ·
      refine ⟨72032154991428942633524453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48021436660952628422349635 72032154991428942633524453)
      ·
        refine ⟨13506029060892926743785835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72032154991428942633524453 13506029060892926743785835)
        ·
          refine ⟨20259043591339390115678753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13506029060892926743785835 20259043591339390115678753)
          ·
            refine ⟨15194282693504542586759065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20259043591339390115678753 15194282693504542586759065)
            ·
              refine ⟨11395712020128406940069299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15194282693504542586759065 11395712020128406940069299)
              ·
                refine ⟨17093568030192610410103949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11395712020128406940069299 17093568030192610410103949)
                ·
                  refine ⟨6410088011322228903788981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17093568030192610410103949 6410088011322228903788981)
                  ·
                    refine ⟨600945751061458959730217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6410088011322228903788981 600945751061458959730217)
                    ·
                      rfl

theorem cell23_3511013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_3511013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511013 prefixEnd_3511013 := by exact prefixLift 3511013
  have htrace : WordTrace (prefixWord ++ tailWord_3511013) baseStart_3511013 baseEnd_3511013 := by
    simpa [prefixWord, tailWord_3511013, baseEnd_3511013] using wordTrace_append hprefix tailTrace_3511013
  have hstable : (prefixWord ++ tailWord_3511013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511013).length < 2 ^ (prefixWord ++ tailWord_3511013).sum := by decide
  have hdescent : baseEnd_3511013 < baseStart_3511013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511030 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3511030 : Nat := 118140960795 + 3511030 * 2 ^ 59
def prefixEnd_3511030 : Nat := 4983230072969 + 3 ^ 40 * 3511030 * 2
def baseEnd_3511030 : Nat := 600948660785167770892691

theorem tailTrace_3511030 : CollatzResearch.WordTrace tailWord_3511030 prefixEnd_3511030 600948660785167770892691 := by
  unfold tailWord_3511030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003611529384088814352159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85371856313430280686423029 8003611529384088814352159)
  ·
    refine ⟨12005417294076133221528239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8003611529384088814352159 12005417294076133221528239)
    ·
      refine ⟨18008125941114199832292359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12005417294076133221528239 18008125941114199832292359)
      ·
        refine ⟨27012188911671299748438539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18008125941114199832292359 27012188911671299748438539)
        ·
          refine ⟨40518283367506949622657809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27012188911671299748438539 40518283367506949622657809)
          ·
            refine ⟨30388712525630212216993357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40518283367506949622657809 30388712525630212216993357)
            ·
              refine ⟨11395767197111329581372509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30388712525630212216993357 11395767197111329581372509)
              ·
                refine ⟨4273412698916748593014691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11395767197111329581372509 4273412698916748593014691)
                ·
                  refine ⟨6410119048375122889522037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273412698916748593014691 6410119048375122889522037)
                  ·
                    refine ⟨600948660785167770892691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6410119048375122889522037 600948660785167770892691)
                    ·
                      rfl

theorem cell23_3511030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3511030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511030 prefixEnd_3511030 := by exact prefixLift 3511030
  have htrace : WordTrace (prefixWord ++ tailWord_3511030) baseStart_3511030 baseEnd_3511030 := by
    simpa [prefixWord, tailWord_3511030, baseEnd_3511030] using wordTrace_append hprefix tailTrace_3511030
  have hstable : (prefixWord ++ tailWord_3511030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511030).length < 2 ^ (prefixWord ++ tailWord_3511030).sum := by decide
  have hdescent : baseEnd_3511030 < baseStart_3511030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511033 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 8, 2]
def baseStart_3511033 : Nat := 118140960795 + 3511033 * 2 ^ 59
def prefixEnd_3511033 : Nat := 4983230072969 + 3 ^ 40 * 3511033 * 2
def baseEnd_3511033 : Nat := 1802847522797466800940559

theorem tailTrace_3511033 : CollatzResearch.WordTrace tailWord_3511033 prefixEnd_3511033 1802847522797466800940559 := by
  unfold tailWord_3511033
  simp only [CollatzResearch.WordTrace]
  refine ⟨128057893889134552541993753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85371929259423035027995835 128057893889134552541993753)
  ·
    refine ⟨96043420416850914406495315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128057893889134552541993753 96043420416850914406495315)
    ·
      refine ⟨144065130625276371609742973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96043420416850914406495315 144065130625276371609742973)
      ·
        refine ⟨54024423984478639353653615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144065130625276371609742973 54024423984478639353653615)
        ·
          refine ⟨81036635976717959030480423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54024423984478639353653615 81036635976717959030480423)
          ·
            refine ⟨121554953965076938545720635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81036635976717959030480423 121554953965076938545720635)
            ·
              refine ⟨182332430947615407818580953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121554953965076938545720635 182332430947615407818580953)
              ·
                refine ⟨136749323210711555863935715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182332430947615407818580953 136749323210711555863935715)
                ·
                  refine ⟨205123984816067333795903573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136749323210711555863935715 205123984816067333795903573)
                  ·
                    refine ⟨2403796697063289067920745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 205123984816067333795903573 2403796697063289067920745)
                    ·
                      refine ⟨1802847522797466800940559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403796697063289067920745 1802847522797466800940559)
                      ·
                        rfl

theorem cell23_3511033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_3511033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511033 prefixEnd_3511033 := by exact prefixLift 3511033
  have htrace : WordTrace (prefixWord ++ tailWord_3511033) baseStart_3511033 baseEnd_3511033 := by
    simpa [prefixWord, tailWord_3511033, baseEnd_3511033] using wordTrace_append hprefix tailTrace_3511033
  have hstable : (prefixWord ++ tailWord_3511033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511033).length < 2 ^ (prefixWord ++ tailWord_3511033).sum := by decide
  have hdescent : baseEnd_3511033 < baseStart_3511033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511101 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3511101 : Nat := 118140960795 + 3511101 * 2 ^ 59
def prefixEnd_3511101 : Nat := 4983230072969 + 3 ^ 40 * 3511101 * 2
def baseEnd_3511101 : Nat := 1802882439481972534890247

theorem tailTrace_3511101 : CollatzResearch.WordTrace tailWord_3511101 prefixEnd_3511101 1802882439481972534890247 := by
  unfold tailWord_3511101
  simp only [CollatzResearch.WordTrace]
  refine ⟨128060374052888200155469157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85373582701925466770312771 128060374052888200155469157)
  ·
    refine ⟨24011320134916537529150467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128060374052888200155469157 24011320134916537529150467)
    ·
      refine ⟨36016980202374806293725701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24011320134916537529150467 36016980202374806293725701)
      ·
        refine ⟨6753183787945276180073569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36016980202374806293725701 6753183787945276180073569)
        ·
          refine ⟨5064887840958957135055177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6753183787945276180073569 5064887840958957135055177)
          ·
            refine ⟨3798665880719217851291383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064887840958957135055177 3798665880719217851291383)
            ·
              refine ⟨5697998821078826776937075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798665880719217851291383 5697998821078826776937075)
              ·
                refine ⟨8546998231618240165405613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697998821078826776937075 8546998231618240165405613)
                ·
                  refine ⟨3205124336856840062027105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8546998231618240165405613 3205124336856840062027105)
                  ·
                    refine ⟨2403843252642630046520329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205124336856840062027105 2403843252642630046520329)
                    ·
                      refine ⟨1802882439481972534890247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403843252642630046520329 1802882439481972534890247)
                      ·
                        rfl

theorem cell23_3511101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3511101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511101 prefixEnd_3511101 := by exact prefixLift 3511101
  have htrace : WordTrace (prefixWord ++ tailWord_3511101) baseStart_3511101 baseEnd_3511101 := by
    simpa [prefixWord, tailWord_3511101, baseEnd_3511101] using wordTrace_append hprefix tailTrace_3511101
  have hstable : (prefixWord ++ tailWord_3511101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511101).length < 2 ^ (prefixWord ++ tailWord_3511101).sum := by decide
  have hdescent : baseEnd_3511101 < baseStart_3511101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511127 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_3511127 : Nat := 118140960795 + 3511127 * 2 ^ 59
def prefixEnd_3511127 : Nat := 4983230072969 + 3 ^ 40 * 3511127 * 2
def baseEnd_3511127 : Nat := 1802895789978989433165127

theorem tailTrace_3511127 : CollatzResearch.WordTrace tailWord_3511127 prefixEnd_3511127 1802895789978989433165127 := by
  unfold tailWord_3511127
  simp only [CollatzResearch.WordTrace]
  refine ⟨128061322350794006595915635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85374214900529337730610423 128061322350794006595915635)
  ·
    refine ⟨192091983526191009893873453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128061322350794006595915635 192091983526191009893873453)
    ·
      refine ⟨72034493822321628710202545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192091983526191009893873453 72034493822321628710202545)
      ·
        refine ⟨54025870366741221532651909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72034493822321628710202545 54025870366741221532651909)
        ·
          refine ⟨10129850693763979037372233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54025870366741221532651909 10129850693763979037372233)
          ·
            refine ⟨7597388020322984278029175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10129850693763979037372233 7597388020322984278029175)
            ·
              refine ⟨11396082030484476417043763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597388020322984278029175 11396082030484476417043763)
              ·
                refine ⟨17094123045726714625565645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396082030484476417043763 17094123045726714625565645)
                ·
                  refine ⟨6410296142147517984587117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17094123045726714625565645 6410296142147517984587117)
                  ·
                    refine ⟨2403861053305319244220169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6410296142147517984587117 2403861053305319244220169)
                    ·
                      refine ⟨1802895789978989433165127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2403861053305319244220169 1802895789978989433165127)
                      ·
                        rfl

theorem cell23_3511127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_3511127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511127 prefixEnd_3511127 := by exact prefixLift 3511127
  have htrace : WordTrace (prefixWord ++ tailWord_3511127) baseStart_3511127 baseEnd_3511127 := by
    simpa [prefixWord, tailWord_3511127, baseEnd_3511127] using wordTrace_append hprefix tailTrace_3511127
  have hstable : (prefixWord ++ tailWord_3511127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511127).length < 2 ^ (prefixWord ++ tailWord_3511127).sum := by decide
  have hdescent : baseEnd_3511127 < baseStart_3511127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511197 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 5]
def baseStart_3511197 : Nat := 118140960795 + 3511197 * 2 ^ 59
def prefixEnd_3511197 : Nat := 4983230072969 + 3 ^ 40 * 3511197 * 2
def baseEnd_3511197 : Nat := 200325748180533795476645

theorem tailTrace_3511197 : CollatzResearch.WordTrace tailWord_3511197 prefixEnd_3511197 200325748180533795476645 := by
  unfold tailWord_3511197
  simp only [CollatzResearch.WordTrace]
  refine ⟨128063875460540408550963845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85375916973693605700642563 128063875460540408550963845)
  ·
    refine ⟨24011976648851326603305721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128063875460540408550963845 24011976648851326603305721)
    ·
      refine ⟨18008982486638494952479291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24011976648851326603305721 18008982486638494952479291)
      ·
        refine ⟨27013473729957742428718937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18008982486638494952479291 27013473729957742428718937)
        ·
          refine ⟨20260105297468306821539203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27013473729957742428718937 20260105297468306821539203)
          ·
            refine ⟨30390157946202460232308805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20260105297468306821539203 30390157946202460232308805)
            ·
              refine ⟨5698154614912961293557901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30390157946202460232308805 5698154614912961293557901)
              ·
                refine ⟨2136807980592360485084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698154614912961293557901 2136807980592360485084213)
                ·
                  refine ⟨200325748180533795476645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2136807980592360485084213 200325748180533795476645)
                  ·
                    rfl

theorem cell23_3511197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_3511197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511197 prefixEnd_3511197 := by exact prefixLift 3511197
  have htrace : WordTrace (prefixWord ++ tailWord_3511197) baseStart_3511197 baseEnd_3511197 := by
    simpa [prefixWord, tailWord_3511197, baseEnd_3511197] using wordTrace_append hprefix tailTrace_3511197
  have hstable : (prefixWord ++ tailWord_3511197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511197).length < 2 ^ (prefixWord ++ tailWord_3511197).sum := by decide
  have hdescent : baseEnd_3511197 < baseStart_3511197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511203 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3511203 : Nat := 118140960795 + 3511203 * 2 ^ 59
def prefixEnd_3511203 : Nat := 4983230072969 + 3 ^ 40 * 3511203 * 2
def baseEnd_3511203 : Nat := 1802934814508731135814777

theorem tailTrace_3511203 : CollatzResearch.WordTrace tailWord_3511203 prefixEnd_3511203 1802934814508731135814777 := by
  unfold tailWord_3511203
  simp only [CollatzResearch.WordTrace]
  refine ⟨128064094298518671575682263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85376062865679114383788175 128064094298518671575682263)
  ·
    refine ⟨192096141447778007363523395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128064094298518671575682263 192096141447778007363523395)
    ·
      refine ⟨288144212171667011045285093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192096141447778007363523395 288144212171667011045285093)
      ·
        refine ⟨54027039782187564570990955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288144212171667011045285093 54027039782187564570990955)
        ·
          refine ⟨81040559673281346856486433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54027039782187564570990955 81040559673281346856486433)
          ·
            refine ⟨60780419754961010142364825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81040559673281346856486433 60780419754961010142364825)
            ·
              refine ⟨45585314816220757606773619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60780419754961010142364825 45585314816220757606773619)
              ·
                refine ⟨68377972224331136410160429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45585314816220757606773619 68377972224331136410160429)
                ·
                  refine ⟨25641739584124176153810161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68377972224331136410160429 25641739584124176153810161)
                  ·
                    refine ⟨19231304688093132115357621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25641739584124176153810161 19231304688093132115357621)
                    ·
                      refine ⟨1802934814508731135814777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19231304688093132115357621 1802934814508731135814777)
                      ·
                        rfl

theorem cell23_3511203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3511203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511203 prefixEnd_3511203 := by exact prefixLift 3511203
  have htrace : WordTrace (prefixWord ++ tailWord_3511203) baseStart_3511203 baseEnd_3511203 := by
    simpa [prefixWord, tailWord_3511203, baseEnd_3511203] using wordTrace_append hprefix tailTrace_3511203
  have hstable : (prefixWord ++ tailWord_3511203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511203).length < 2 ^ (prefixWord ++ tailWord_3511203).sum := by decide
  have hdescent : baseEnd_3511203 < baseStart_3511203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511230 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3511230 : Nat := 118140960795 + 3511230 * 2 ^ 59
def prefixEnd_3511230 : Nat := 4983230072969 + 3 ^ 40 * 3511230 * 2
def baseEnd_3511230 : Nat := 1802948678486402530177153

theorem tailTrace_3511230 : CollatzResearch.WordTrace tailWord_3511230 prefixEnd_3511230 1802948678486402530177153 := by
  unfold tailWord_3511230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008134883677606898364393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85376719379613903457943429 16008134883677606898364393)
  ·
    refine ⟨12006101162758205173773295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16008134883677606898364393 12006101162758205173773295)
    ·
      refine ⟨18009151744137307760659943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006101162758205173773295 18009151744137307760659943)
      ·
        refine ⟨27013727616205961640989915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18009151744137307760659943 27013727616205961640989915)
        ·
          refine ⟨40520591424308942461484873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27013727616205961640989915 40520591424308942461484873)
          ·
            refine ⟨30390443568231706846113655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40520591424308942461484873 30390443568231706846113655)
            ·
              refine ⟨45585665352347560269170483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30390443568231706846113655 45585665352347560269170483)
              ·
                refine ⟨68378498028521340403755725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45585665352347560269170483 68378498028521340403755725)
                ·
                  refine ⟨25641936760695502651408397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68378498028521340403755725 25641936760695502651408397)
                  ·
                    refine ⟨9615726285260813494278149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25641936760695502651408397 9615726285260813494278149)
                    ·
                      refine ⟨1802948678486402530177153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9615726285260813494278149 1802948678486402530177153)
                      ·
                        rfl

theorem cell23_3511230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3511230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511230 prefixEnd_3511230 := by exact prefixLift 3511230
  have htrace : WordTrace (prefixWord ++ tailWord_3511230) baseStart_3511230 baseEnd_3511230 := by
    simpa [prefixWord, tailWord_3511230, baseEnd_3511230] using wordTrace_append hprefix tailTrace_3511230
  have hstable : (prefixWord ++ tailWord_3511230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511230).length < 2 ^ (prefixWord ++ tailWord_3511230).sum := by decide
  have hdescent : baseEnd_3511230 < baseStart_3511230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511267 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3511267 : Nat := 118140960795 + 3511267 * 2 ^ 59
def prefixEnd_3511267 : Nat := 4983230072969 + 3 ^ 40 * 3511267 * 2
def baseEnd_3511267 : Nat := 1802967677270618885414483

theorem tailTrace_3511267 : CollatzResearch.WordTrace tailWord_3511267 prefixEnd_3511267 1802967677270618885414483 := by
  unfold tailWord_3511267
  simp only [CollatzResearch.WordTrace]
  refine ⟨128066428570286810506012055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85377619046857873670674703 128066428570286810506012055)
  ·
    refine ⟨192099642855430215759018083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128066428570286810506012055 192099642855430215759018083)
    ·
      refine ⟨288149464283145323638527125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192099642855430215759018083 288149464283145323638527125)
      ·
        refine ⟨13507006138272437045555959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288149464283145323638527125 13507006138272437045555959)
        ·
          refine ⟨20260509207408655568333939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507006138272437045555959 20260509207408655568333939)
          ·
            refine ⟨30390763811112983352500909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20260509207408655568333939 30390763811112983352500909)
            ·
              refine ⟨11396536429167368757187841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30390763811112983352500909 11396536429167368757187841)
              ·
                refine ⟨8547402321875526567890881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396536429167368757187841 8547402321875526567890881)
                ·
                  refine ⟨6410551741406644925918161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547402321875526567890881 6410551741406644925918161)
                  ·
                    refine ⟨4807913806054983694438621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410551741406644925918161 4807913806054983694438621)
                    ·
                      refine ⟨1802967677270618885414483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4807913806054983694438621 1802967677270618885414483)
                      ·
                        rfl

theorem cell23_3511267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3511267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511267 prefixEnd_3511267 := by exact prefixLift 3511267
  have htrace : WordTrace (prefixWord ++ tailWord_3511267) baseStart_3511267 baseEnd_3511267 := by
    simpa [prefixWord, tailWord_3511267, baseEnd_3511267] using wordTrace_append hprefix tailTrace_3511267
  have hstable : (prefixWord ++ tailWord_3511267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511267).length < 2 ^ (prefixWord ++ tailWord_3511267).sum := by decide
  have hdescent : baseEnd_3511267 < baseStart_3511267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511274 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3511274 : Nat := 118140960795 + 3511274 * 2 ^ 59
def prefixEnd_3511274 : Nat := 4983230072969 + 3 ^ 40 * 3511274 * 2
def baseEnd_3511274 : Nat := 600990423878400119342317

theorem tailTrace_3511274 : CollatzResearch.WordTrace tailWord_3511274 prefixEnd_3511274 600990423878400119342317 := by
  unfold tailWord_3511274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32016670970315362675379219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85377789254174300467677917 32016670970315362675379219)
  ·
    refine ⟨48025006455473044013068829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32016670970315362675379219 48025006455473044013068829)
    ·
      refine ⟨18009377420802391504900811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48025006455473044013068829 18009377420802391504900811)
      ·
        refine ⟨27014066131203587257351217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18009377420802391504900811 27014066131203587257351217)
        ·
          refine ⟨20260549598402690443013413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27014066131203587257351217 20260549598402690443013413)
          ·
            refine ⟨3798853049700504458065015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20260549598402690443013413 3798853049700504458065015)
            ·
              refine ⟨5698279574550756687097523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798853049700504458065015 5698279574550756687097523)
              ·
                refine ⟨8547419361826135030646285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698279574550756687097523 8547419361826135030646285)
                ·
                  refine ⟨3205282260684800636492357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8547419361826135030646285 3205282260684800636492357)
                  ·
                    refine ⟨600990423878400119342317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205282260684800636492357 600990423878400119342317)
                    ·
                      rfl

theorem cell23_3511274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3511274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511274 prefixEnd_3511274 := by exact prefixLift 3511274
  have htrace : WordTrace (prefixWord ++ tailWord_3511274) baseStart_3511274 baseEnd_3511274 := by
    simpa [prefixWord, tailWord_3511274, baseEnd_3511274] using wordTrace_append hprefix tailTrace_3511274
  have hstable : (prefixWord ++ tailWord_3511274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511274).length < 2 ^ (prefixWord ++ tailWord_3511274).sum := by decide
  have hdescent : baseEnd_3511274 < baseStart_3511274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511283 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 11]
def baseStart_3511283 : Nat := 118140960795 + 3511283 * 2 ^ 59
def prefixEnd_3511283 : Nat := 4983230072969 + 3 ^ 40 * 3511283 * 2
def baseEnd_3511283 : Nat := 600991964320363607604803

theorem tailTrace_3511283 : CollatzResearch.WordTrace tailWord_3511283 prefixEnd_3511283 600991964320363607604803 := by
  unfold tailWord_3511283
  simp only [CollatzResearch.WordTrace]
  refine ⟨128067012138228845238594503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85378008092152563492396335 128067012138228845238594503)
  ·
    refine ⟨192100518207343267857891755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128067012138228845238594503 192100518207343267857891755)
    ·
      refine ⟨288150777311014901786837633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192100518207343267857891755 288150777311014901786837633)
      ·
        refine ⟨216113082983261176340128225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288150777311014901786837633 216113082983261176340128225)
        ·
          refine ⟨162084812237445882255096169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216113082983261176340128225 162084812237445882255096169)
          ·
            refine ⟨121563609178084411691322127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162084812237445882255096169 121563609178084411691322127)
            ·
              refine ⟨182345413767126617536983191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121563609178084411691322127 182345413767126617536983191)
              ·
                refine ⟨273518120650689926305474787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182345413767126617536983191 273518120650689926305474787)
                ·
                  refine ⟨410277180976034889458212181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273518120650689926305474787 410277180976034889458212181)
                  ·
                    refine ⟨600991964320363607604803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 410277180976034889458212181 600991964320363607604803)
                    ·
                      rfl

theorem cell23_3511283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_3511283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511283 prefixEnd_3511283 := by exact prefixLift 3511283
  have htrace : WordTrace (prefixWord ++ tailWord_3511283) baseStart_3511283 baseEnd_3511283 := by
    simpa [prefixWord, tailWord_3511283, baseEnd_3511283] using wordTrace_append hprefix tailTrace_3511283
  have hstable : (prefixWord ++ tailWord_3511283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511283).length < 2 ^ (prefixWord ++ tailWord_3511283).sum := by decide
  have hdescent : baseEnd_3511283 < baseStart_3511283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511325 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3511325 : Nat := 118140960795 + 3511325 * 2 ^ 59
def prefixEnd_3511325 : Nat := 4983230072969 + 3 ^ 40 * 3511325 * 2
def baseEnd_3511325 : Nat := 600999153049526552829739

theorem tailTrace_3511325 : CollatzResearch.WordTrace tailWord_3511325 prefixEnd_3511325 600999153049526552829739 := by
  unfold tailWord_3511325
  simp only [CollatzResearch.WordTrace]
  refine ⟨128068544004076686411623429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85379029336051124274415619 128068544004076686411623429)
  ·
    refine ⟨24012852000764378702179393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128068544004076686411623429 24012852000764378702179393)
    ·
      refine ⟨18009639000573284026634545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24012852000764378702179393 18009639000573284026634545)
      ·
        refine ⟨13507229250429963019975909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18009639000573284026634545 13507229250429963019975909)
        ·
          refine ⟨2532605484455618066245483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13507229250429963019975909 2532605484455618066245483)
          ·
            refine ⟨3798908226683427099368225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532605484455618066245483 3798908226683427099368225)
            ·
              refine ⟨2849181170012570324526169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798908226683427099368225 2849181170012570324526169)
              ·
                refine ⟨2136885877509427743394627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849181170012570324526169 2136885877509427743394627)
                ·
                  refine ⟨3205328816264141615091941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136885877509427743394627 3205328816264141615091941)
                  ·
                    refine ⟨600999153049526552829739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205328816264141615091941 600999153049526552829739)
                    ·
                      rfl

theorem cell23_3511325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3511325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511325 prefixEnd_3511325 := by exact prefixLift 3511325
  have htrace : WordTrace (prefixWord ++ tailWord_3511325) baseStart_3511325 baseEnd_3511325 := by
    simpa [prefixWord, tailWord_3511325, baseEnd_3511325] using wordTrace_append hprefix tailTrace_3511325
  have hstable : (prefixWord ++ tailWord_3511325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511325).length < 2 ^ (prefixWord ++ tailWord_3511325).sum := by decide
  have hdescent : baseEnd_3511325 < baseStart_3511325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511331 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 1, 1, 3]
def baseStart_3511331 : Nat := 118140960795 + 3511331 * 2 ^ 59
def prefixEnd_3511331 : Nat := 4983230072969 + 3 ^ 40 * 3511331 * 2
def baseEnd_3511331 : Nat := 1803000540032506635014189

theorem tailTrace_3511331 : CollatzResearch.WordTrace tailWord_3511331 prefixEnd_3511331 1803000540032506635014189 := by
  unfold tailWord_3511331
  simp only [CollatzResearch.WordTrace]
  refine ⟨128068762842054949436341847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85379175228036632957561231 128068762842054949436341847)
  ·
    refine ⟨192103144263082424154512771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128068762842054949436341847 192103144263082424154512771)
    ·
      refine ⟨288154716394623636231769157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192103144263082424154512771 288154716394623636231769157)
      ·
        refine ⟨54029009323991931793456717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288154716394623636231769157 54029009323991931793456717)
        ·
          refine ⟨20260878496496974422546269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54029009323991931793456717 20260878496496974422546269)
          ·
            refine ⟨7597829436186365408454851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20260878496496974422546269 7597829436186365408454851)
            ·
              refine ⟨11396744154279548112682277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597829436186365408454851 11396744154279548112682277)
              ·
                refine ⟨2136889528927415271127927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11396744154279548112682277 2136889528927415271127927)
                ·
                  refine ⟨3205334293391122906691891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136889528927415271127927 3205334293391122906691891)
                  ·
                    refine ⟨4808001440086684360037837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205334293391122906691891 4808001440086684360037837)
                    ·
                      refine ⟨1803000540032506635014189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808001440086684360037837 1803000540032506635014189)
                      ·
                        rfl

theorem cell23_3511331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_3511331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511331 prefixEnd_3511331 := by exact prefixLift 3511331
  have htrace : WordTrace (prefixWord ++ tailWord_3511331) baseStart_3511331 baseEnd_3511331 := by
    simpa [prefixWord, tailWord_3511331, baseEnd_3511331] using wordTrace_append hprefix tailTrace_3511331
  have hstable : (prefixWord ++ tailWord_3511331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511331).length < 2 ^ (prefixWord ++ tailWord_3511331).sum := by decide
  have hdescent : baseEnd_3511331 < baseStart_3511331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511340 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3511340 : Nat := 118140960795 + 3511340 * 2 ^ 59
def prefixEnd_3511340 : Nat := 4983230072969 + 3 ^ 40 * 3511340 * 2
def baseEnd_3511340 : Nat := 1803005161358397099801647

theorem tailTrace_3511340 : CollatzResearch.WordTrace tailWord_3511340 prefixEnd_3511340 1803005161358397099801647 := by
  unfold tailWord_3511340
  simp only [CollatzResearch.WordTrace]
  refine ⟨64034545549511171986709737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85379394066014895982279649 64034545549511171986709737)
  ·
    refine ⟨48025909162133378990032303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64034545549511171986709737 48025909162133378990032303)
    ·
      refine ⟨72038863743200068485048455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48025909162133378990032303 72038863743200068485048455)
      ·
        refine ⟨108058295614800102727572683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72038863743200068485048455 108058295614800102727572683)
        ·
          refine ⟨162087443422200154091359025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108058295614800102727572683 162087443422200154091359025)
          ·
            refine ⟨121565582566650115568519269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162087443422200154091359025 121565582566650115568519269)
            ·
              refine ⟨22793546731246896669097363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121565582566650115568519269 22793546731246896669097363)
              ·
                refine ⟨34190320096870345003646045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22793546731246896669097363 34190320096870345003646045)
                ·
                  refine ⟨12821370036326379376367267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34190320096870345003646045 12821370036326379376367267)
                  ·
                    refine ⟨19232055054489569064550901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12821370036326379376367267 19232055054489569064550901)
                    ·
                      refine ⟨1803005161358397099801647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19232055054489569064550901 1803005161358397099801647)
                      ·
                        rfl

theorem cell23_3511340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3511340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511340 prefixEnd_3511340 := by exact prefixLift 3511340
  have htrace : WordTrace (prefixWord ++ tailWord_3511340) baseStart_3511340 baseEnd_3511340 := by
    simpa [prefixWord, tailWord_3511340, baseEnd_3511340] using wordTrace_append hprefix tailTrace_3511340
  have hstable : (prefixWord ++ tailWord_3511340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511340).length < 2 ^ (prefixWord ++ tailWord_3511340).sum := by decide
  have hdescent : baseEnd_3511340 < baseStart_3511340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511354 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_3511354 : Nat := 118140960795 + 3511354 * 2 ^ 59
def prefixEnd_3511354 : Nat := 4983230072969 + 3 ^ 40 * 3511354 * 2
def baseEnd_3511354 : Nat := 1803012350087560045026583

theorem tailTrace_3511354 : CollatzResearch.WordTrace tailWord_3511354 prefixEnd_3511354 1803012350087560045026583 := by
  unfold tailWord_3511354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32017400430242906091107279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85379734480647749576286077 32017400430242906091107279)
  ·
    refine ⟨48026100645364359136660919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32017400430242906091107279 48026100645364359136660919)
    ·
      refine ⟨72039150968046538704991379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48026100645364359136660919 72039150968046538704991379)
      ·
        refine ⟨108058726452069808057487069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72039150968046538704991379 108058726452069808057487069)
        ·
          refine ⟨40522022419526178021557651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108058726452069808057487069 40522022419526178021557651)
          ·
            refine ⟨60783033629289267032336477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40522022419526178021557651 60783033629289267032336477)
            ·
              refine ⟨22793637610983475137126179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60783033629289267032336477 22793637610983475137126179)
              ·
                refine ⟨34190456416475212705689269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22793637610983475137126179 34190456416475212705689269)
                ·
                  refine ⟨3205355289044551191158369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34190456416475212705689269 3205355289044551191158369)
                  ·
                    refine ⟨2404016466783413393368777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205355289044551191158369 2404016466783413393368777)
                    ·
                      refine ⟨1803012350087560045026583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404016466783413393368777 1803012350087560045026583)
                      ·
                        rfl

theorem cell23_3511354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_3511354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511354 prefixEnd_3511354 := by exact prefixLift 3511354
  have htrace : WordTrace (prefixWord ++ tailWord_3511354) baseStart_3511354 baseEnd_3511354 := by
    simpa [prefixWord, tailWord_3511354, baseEnd_3511354] using wordTrace_append hprefix tailTrace_3511354
  have hstable : (prefixWord ++ tailWord_3511354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511354).length < 2 ^ (prefixWord ++ tailWord_3511354).sum := by decide
  have hdescent : baseEnd_3511354 < baseStart_3511354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511358 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3511358 : Nat := 118140960795 + 3511358 * 2 ^ 59
def prefixEnd_3511358 : Nat := 4983230072969 + 3 ^ 40 * 3511358 * 2
def baseEnd_3511358 : Nat := 1803014404010178029376565

theorem tailTrace_3511358 : CollatzResearch.WordTrace tailWord_3511358 prefixEnd_3511358 1803014404010178029376565 := by
  unfold tailWord_3511358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008718451619641630946841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85379831741971422031716485 16008718451619641630946841)
  ·
    refine ⟨12006538838714731223210131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16008718451619641630946841 12006538838714731223210131)
    ·
      refine ⟨18009808258072096834815197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006538838714731223210131 18009808258072096834815197)
      ·
        refine ⟨6753678096777036313055699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18009808258072096834815197 6753678096777036313055699)
        ·
          refine ⟨10130517145165554469583549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753678096777036313055699 10130517145165554469583549)
          ·
            refine ⟨3798943929437082926093831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10130517145165554469583549 3798943929437082926093831)
            ·
              refine ⟨5698415894155624389140747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798943929437082926093831 5698415894155624389140747)
              ·
                refine ⟨8547623841233436583711121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698415894155624389140747 8547623841233436583711121)
                ·
                  refine ⟨6410717880925077437783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547623841233436583711121 6410717880925077437783341)
                  ·
                    refine ⟨2404019205346904039168753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6410717880925077437783341 2404019205346904039168753)
                    ·
                      refine ⟨1803014404010178029376565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404019205346904039168753 1803014404010178029376565)
                      ·
                        rfl

theorem cell23_3511358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3511358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511358 prefixEnd_3511358 := by exact prefixLift 3511358
  have htrace : WordTrace (prefixWord ++ tailWord_3511358) baseStart_3511358 baseEnd_3511358 := by
    simpa [prefixWord, tailWord_3511358, baseEnd_3511358] using wordTrace_append hprefix tailTrace_3511358
  have hstable : (prefixWord ++ tailWord_3511358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511358).length < 2 ^ (prefixWord ++ tailWord_3511358).sum := by decide
  have hdescent : baseEnd_3511358 < baseStart_3511358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511367 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3511367 : Nat := 118140960795 + 3511367 * 2 ^ 59
def prefixEnd_3511367 : Nat := 4983230072969 + 3 ^ 40 * 3511367 * 2
def baseEnd_3511367 : Nat := 1803019025336068494164023

theorem tailTrace_3511367 : CollatzResearch.WordTrace tailWord_3511367 prefixEnd_3511367 1803019025336068494164023 := by
  unfold tailWord_3511367
  simp only [CollatzResearch.WordTrace]
  refine ⟨128070075869924527584652355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85380050579949685056434903 128070075869924527584652355)
  ·
    refine ⟨192105113804886791376978533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128070075869924527584652355 192105113804886791376978533)
    ·
      refine ⟨36019708838416273383183475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192105113804886791376978533 36019708838416273383183475)
      ·
        refine ⟨54029563257624410074775213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36019708838416273383183475 54029563257624410074775213)
        ·
          refine ⟨20261086221609153778040705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54029563257624410074775213 20261086221609153778040705)
          ·
            refine ⟨15195814666206865333530529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20261086221609153778040705 15195814666206865333530529)
            ·
              refine ⟨11396860999655149000147897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15195814666206865333530529 11396860999655149000147897)
              ·
                refine ⟨8547645749741361750110923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396860999655149000147897 8547645749741361750110923)
                ·
                  refine ⟨12821468624612042625166385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8547645749741361750110923 12821468624612042625166385)
                  ·
                    refine ⟨9616101468459031968874789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12821468624612042625166385 9616101468459031968874789)
                    ·
                      refine ⟨1803019025336068494164023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9616101468459031968874789 1803019025336068494164023)
                      ·
                        rfl

theorem cell23_3511367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3511367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511367 prefixEnd_3511367 := by exact prefixLift 3511367
  have htrace : WordTrace (prefixWord ++ tailWord_3511367) baseStart_3511367 baseEnd_3511367 := by
    simpa [prefixWord, tailWord_3511367, baseEnd_3511367] using wordTrace_append hprefix tailTrace_3511367
  have hstable : (prefixWord ++ tailWord_3511367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511367).length < 2 ^ (prefixWord ++ tailWord_3511367).sum := by decide
  have hdescent : baseEnd_3511367 < baseStart_3511367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511374 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3511374 : Nat := 118140960795 + 3511374 * 2 ^ 59
def prefixEnd_3511374 : Nat := 4983230072969 + 3 ^ 40 * 3511374 * 2
def baseEnd_3511374 : Nat := 1803022619700649966776491

theorem tailTrace_3511374 : CollatzResearch.WordTrace tailWord_3511374 prefixEnd_3511374 1803022619700649966776491 := by
  unfold tailWord_3511374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008791397612395972519647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85380220787266111853438117 16008791397612395972519647)
  ·
    refine ⟨24013187096418593958779471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16008791397612395972519647 24013187096418593958779471)
    ·
      refine ⟨36019780644627890938169207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24013187096418593958779471 36019780644627890938169207)
      ·
        refine ⟨54029670966941836407253811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36019780644627890938169207 54029670966941836407253811)
        ·
          refine ⟨81044506450412754610880717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54029670966941836407253811 81044506450412754610880717)
          ·
            refine ⟨30391689918904782979080269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81044506450412754610880717 30391689918904782979080269)
            ·
              refine ⟨11396883719589293617155101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30391689918904782979080269 11396883719589293617155101)
              ·
                refine ⟨4273831394845985106433163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11396883719589293617155101 4273831394845985106433163)
                ·
                  refine ⟨6410747092268977659649745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273831394845985106433163 6410747092268977659649745)
                  ·
                    refine ⟨4808060319201733244737309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410747092268977659649745 4808060319201733244737309)
                    ·
                      refine ⟨1803022619700649966776491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808060319201733244737309 1803022619700649966776491)
                      ·
                        rfl

theorem cell23_3511374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3511374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511374 prefixEnd_3511374 := by exact prefixLift 3511374
  have htrace : WordTrace (prefixWord ++ tailWord_3511374) baseStart_3511374 baseEnd_3511374 := by
    simpa [prefixWord, tailWord_3511374, baseEnd_3511374] using wordTrace_append hprefix tailTrace_3511374
  have hstable : (prefixWord ++ tailWord_3511374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511374).length < 2 ^ (prefixWord ++ tailWord_3511374).sum := by decide
  have hdescent : baseEnd_3511374 < baseStart_3511374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511388 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_3511388 : Nat := 118140960795 + 3511388 * 2 ^ 59
def prefixEnd_3511388 : Nat := 4983230072969 + 3 ^ 40 * 3511388 * 2
def baseEnd_3511388 : Nat := 1803029808429812912001427

theorem tailTrace_3511388 : CollatzResearch.WordTrace tailWord_3511388 prefixEnd_3511388 1803029808429812912001427 := by
  unfold tailWord_3511388
  simp only [CollatzResearch.WordTrace]
  refine ⟨64035420901424224085583409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85380561201898965447444545 64035420901424224085583409)
  ·
    refine ⟨48026565676068168064187557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64035420901424224085583409 48026565676068168064187557)
    ·
      refine ⟨9004981064262781512035167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48026565676068168064187557 9004981064262781512035167)
      ·
        refine ⟨13507471596394172268052751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9004981064262781512035167 13507471596394172268052751)
        ·
          refine ⟨20261207394591258402079127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507471596394172268052751 20261207394591258402079127)
          ·
            refine ⟨30391811091886887603118691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261207394591258402079127 30391811091886887603118691)
            ·
              refine ⟨45587716637830331404678037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30391811091886887603118691 45587716637830331404678037)
              ·
                refine ⟨2136924217398296784594283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45587716637830331404678037 2136924217398296784594283)
                ·
                  refine ⟨3205386326097445176891425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136924217398296784594283 3205386326097445176891425)
                  ·
                    refine ⟨2404039744573083882668569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205386326097445176891425 2404039744573083882668569)
                    ·
                      refine ⟨1803029808429812912001427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404039744573083882668569 1803029808429812912001427)
                      ·
                        rfl

theorem cell23_3511388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_3511388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511388 prefixEnd_3511388 := by exact prefixLift 3511388
  have htrace : WordTrace (prefixWord ++ tailWord_3511388) baseStart_3511388 baseEnd_3511388 := by
    simpa [prefixWord, tailWord_3511388, baseEnd_3511388] using wordTrace_append hprefix tailTrace_3511388
  have hstable : (prefixWord ++ tailWord_3511388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511388).length < 2 ^ (prefixWord ++ tailWord_3511388).sum := by decide
  have hdescent : baseEnd_3511388 < baseStart_3511388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511440 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_3511440 : Nat := 118140960795 + 3511440 * 2 ^ 59
def prefixEnd_3511440 : Nat := 4983230072969 + 3 ^ 40 * 3511440 * 2
def baseEnd_3511440 : Nat := 1803056509423846708551187

theorem tailTrace_3511440 : CollatzResearch.WordTrace tailWord_3511440 prefixEnd_3511440 1803056509423846708551187 := by
  unfold tailWord_3511440
  simp only [CollatzResearch.WordTrace]
  refine ⟨64036369199330030526029887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85381825599106707368039849 64036369199330030526029887)
  ·
    refine ⟨96054553798995045789044831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64036369199330030526029887 96054553798995045789044831)
    ·
      refine ⟨144081830698492568683567247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96054553798995045789044831 144081830698492568683567247)
      ·
        refine ⟨216122746047738853025350871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144081830698492568683567247 216122746047738853025350871)
        ·
          refine ⟨324184119071608279538026307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216122746047738853025350871 324184119071608279538026307)
          ·
            refine ⟨486276178607412419307039461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324184119071608279538026307 486276178607412419307039461)
            ·
              refine ⟨91176783488889828620069899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 486276178607412419307039461 91176783488889828620069899)
              ·
                refine ⟨136765175233334742930104849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91176783488889828620069899 136765175233334742930104849)
                ·
                  refine ⟨102573881425001057197578637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136765175233334742930104849 102573881425001057197578637)
                  ·
                    refine ⟨38465205534375396449091989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102573881425001057197578637 38465205534375396449091989)
                    ·
                      refine ⟨1803056509423846708551187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38465205534375396449091989 1803056509423846708551187)
                      ·
                        rfl

theorem cell23_3511440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_3511440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511440 prefixEnd_3511440 := by exact prefixLift 3511440
  have htrace : WordTrace (prefixWord ++ tailWord_3511440) baseStart_3511440 baseEnd_3511440 := by
    simpa [prefixWord, tailWord_3511440, baseEnd_3511440] using wordTrace_append hprefix tailTrace_3511440
  have hstable : (prefixWord ++ tailWord_3511440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511440).length < 2 ^ (prefixWord ++ tailWord_3511440).sum := by decide
  have hdescent : baseEnd_3511440 < baseStart_3511440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511455 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3511455 : Nat := 118140960795 + 3511455 * 2 ^ 59
def prefixEnd_3511455 : Nat := 4983230072969 + 3 ^ 40 * 3511455 * 2
def baseEnd_3511455 : Nat := 1803064211633664149863619

theorem tailTrace_3511455 : CollatzResearch.WordTrace tailWord_3511455 prefixEnd_3511455 1803064211633664149863619 := by
  unfold tailWord_3511455
  simp only [CollatzResearch.WordTrace]
  refine ⟨128073285493605718613855819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85382190329070479075903879 128073285493605718613855819)
  ·
    refine ⟨192109928240408577920783729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128073285493605718613855819 192109928240408577920783729)
    ·
      refine ⟨144082446180306433440587797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192109928240408577920783729 144082446180306433440587797)
      ·
        refine ⟨6753864664701864067527553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144082446180306433440587797 6753864664701864067527553)
        ·
          refine ⟨5065398498526398050645665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6753864664701864067527553 5065398498526398050645665)
          ·
            refine ⟨3799048873894798537984249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065398498526398050645665 3799048873894798537984249)
            ·
              refine ⟨2849286655421098903488187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799048873894798537984249 2849286655421098903488187)
              ·
                refine ⟨4273929983131648355232281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849286655421098903488187 4273929983131648355232281)
                ·
                  refine ⟨3205447487348736266424211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273929983131648355232281 3205447487348736266424211)
                  ·
                    refine ⟨4808171231023104399636317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205447487348736266424211 4808171231023104399636317)
                    ·
                      refine ⟨1803064211633664149863619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808171231023104399636317 1803064211633664149863619)
                      ·
                        rfl

theorem cell23_3511455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3511455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511455 prefixEnd_3511455 := by exact prefixLift 3511455
  have htrace : WordTrace (prefixWord ++ tailWord_3511455) baseStart_3511455 baseEnd_3511455 := by
    simpa [prefixWord, tailWord_3511455, baseEnd_3511455] using wordTrace_append hprefix tailTrace_3511455
  have hstable : (prefixWord ++ tailWord_3511455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511455).length < 2 ^ (prefixWord ++ tailWord_3511455).sum := by decide
  have hdescent : baseEnd_3511455 < baseStart_3511455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511457 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3511457 : Nat := 118140960795 + 3511457 * 2 ^ 59
def prefixEnd_3511457 : Nat := 4983230072969 + 3 ^ 40 * 3511457 * 2
def baseEnd_3511457 : Nat := 1803065238594973142038609

theorem tailTrace_3511457 : CollatzResearch.WordTrace tailWord_3511457 prefixEnd_3511457 1803065238594973142038609 := by
  unfold tailWord_3511457
  simp only [CollatzResearch.WordTrace]
  refine ⟨128073358439598472955428625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85382238959732315303619083 128073358439598472955428625)
  ·
    refine ⟨96055018829698854716571469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128073358439598472955428625 96055018829698854716571469)
    ·
      refine ⟨36020632061137070518714301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96055018829698854716571469 36020632061137070518714301)
      ·
        refine ⟨13507737022926401444517863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36020632061137070518714301 13507737022926401444517863)
        ·
          refine ⟨20261605534389602166776795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507737022926401444517863 20261605534389602166776795)
          ·
            refine ⟨30392408301584403250165193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261605534389602166776795 30392408301584403250165193)
            ·
              refine ⟨22794306226188302437623895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30392408301584403250165193 22794306226188302437623895)
              ·
                refine ⟨34191459339282453656435843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22794306226188302437623895 34191459339282453656435843)
                ·
                  refine ⟨51287189008923680484653765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34191459339282453656435843 51287189008923680484653765)
                  ·
                    refine ⟨9616347939173190090872581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51287189008923680484653765 9616347939173190090872581)
                    ·
                      refine ⟨1803065238594973142038609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9616347939173190090872581 1803065238594973142038609)
                      ·
                        rfl

theorem cell23_3511457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3511457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511457 prefixEnd_3511457 := by exact prefixLift 3511457
  have htrace : WordTrace (prefixWord ++ tailWord_3511457) baseStart_3511457 baseEnd_3511457 := by
    simpa [prefixWord, tailWord_3511457, baseEnd_3511457] using wordTrace_append hprefix tailTrace_3511457
  have hstable : (prefixWord ++ tailWord_3511457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511457).length < 2 ^ (prefixWord ++ tailWord_3511457).sum := by decide
  have hdescent : baseEnd_3511457 < baseStart_3511457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511557 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 8]
def baseStart_3511557 : Nat := 118140960795 + 3511557 * 2 ^ 59
def prefixEnd_3511557 : Nat := 4983230072969 + 3 ^ 40 * 3511557 * 2
def baseEnd_3511557 : Nat := 200346287406713638976461

theorem tailTrace_3511557 : CollatzResearch.WordTrace tailWord_3511557 prefixEnd_3511557 200346287406713638976461 := by
  unfold tailWord_3511557
  simp only [CollatzResearch.WordTrace]
  refine ⟨128077005739236190034068925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85384670492824126689379283 128077005739236190034068925)
  ·
    refine ⟨48028877152213571262775847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128077005739236190034068925 48028877152213571262775847)
    ·
      refine ⟨72043315728320356894163771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48028877152213571262775847 72043315728320356894163771)
      ·
        refine ⟨108064973592480535341245657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72043315728320356894163771 108064973592480535341245657)
        ·
          refine ⟨81048730194360401505934243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108064973592480535341245657 81048730194360401505934243)
          ·
            refine ⟨121573095291540602258901365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81048730194360401505934243 121573095291540602258901365)
            ·
              refine ⟨11397477683581931461772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121573095291540602258901365 11397477683581931461772003)
              ·
                refine ⟨17096216525372897192658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397477683581931461772003 17096216525372897192658005)
                ·
                  refine ⟨200346287406713638976461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17096216525372897192658005 200346287406713638976461)
                  ·
                    rfl

theorem cell23_3511557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_3511557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511557 prefixEnd_3511557 := by exact prefixLift 3511557
  have htrace : WordTrace (prefixWord ++ tailWord_3511557) baseStart_3511557 baseEnd_3511557 := by
    simpa [prefixWord, tailWord_3511557, baseEnd_3511557] using wordTrace_append hprefix tailTrace_3511557
  have hstable : (prefixWord ++ tailWord_3511557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511557).length < 2 ^ (prefixWord ++ tailWord_3511557).sum := by decide
  have hdescent : baseEnd_3511557 < baseStart_3511557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511561 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 1, 4]
def baseStart_3511561 : Nat := 118140960795 + 3511561 * 2 ^ 59
def prefixEnd_3511561 : Nat := 4983230072969 + 3 ^ 40 * 3511561 * 2
def baseEnd_3511561 : Nat := 601039546861013578379377

theorem tailTrace_3511561 : CollatzResearch.WordTrace tailWord_3511561 prefixEnd_3511561 601039546861013578379377 := by
  unfold tailWord_3511561
  simp only [CollatzResearch.WordTrace]
  refine ⟨128077151631221698717214537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85384767754147799144809691 128077151631221698717214537)
  ·
    refine ⟨96057863723416274037910903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128077151631221698717214537 96057863723416274037910903)
    ·
      refine ⟨144086795585124411056866355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96057863723416274037910903 144086795585124411056866355)
      ·
        refine ⟨216130193377686616585299533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144086795585124411056866355 216130193377686616585299533)
        ·
          refine ⟨81048822516632481219487325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216130193377686616585299533 81048822516632481219487325)
          ·
            refine ⟨30393308443737180457307747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81048822516632481219487325 30393308443737180457307747)
            ·
              refine ⟨45589962665605770685961621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30393308443737180457307747 45589962665605770685961621)
              ·
                refine ⟨2137029499950270500904451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45589962665605770685961621 2137029499950270500904451)
                ·
                  refine ⟨3205544249925405751356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137029499950270500904451 3205544249925405751356677)
                  ·
                    refine ⟨601039546861013578379377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205544249925405751356677 601039546861013578379377)
                    ·
                      rfl

theorem cell23_3511561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 4].length) (baseStart_3511561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511561 prefixEnd_3511561 := by exact prefixLift 3511561
  have htrace : WordTrace (prefixWord ++ tailWord_3511561) baseStart_3511561 baseEnd_3511561 := by
    simpa [prefixWord, tailWord_3511561, baseEnd_3511561] using wordTrace_append hprefix tailTrace_3511561
  have hstable : (prefixWord ++ tailWord_3511561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511561).length < 2 ^ (prefixWord ++ tailWord_3511561).sum := by decide
  have hdescent : baseEnd_3511561 < baseStart_3511561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511624 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3511624 : Nat := 118140960795 + 3511624 * 2 ^ 59
def prefixEnd_3511624 : Nat := 4983230072969 + 3 ^ 40 * 3511624 * 2
def baseEnd_3511624 : Nat := 1803150989864273988650341

theorem tailTrace_3511624 : CollatzResearch.WordTrace tailWord_3511624 prefixEnd_3511624 1803150989864273988650341 := by
  unfold tailWord_3511624
  simp only [CollatzResearch.WordTrace]
  refine ⟨64039724714996730238378963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85386299619995640317838617 64039724714996730238378963)
  ·
    refine ⟨96059587072495095357568445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64039724714996730238378963 96059587072495095357568445)
    ·
      refine ⟨36022345152185660759088167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96059587072495095357568445 36022345152185660759088167)
      ·
        refine ⟨54033517728278491138632251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36022345152185660759088167 54033517728278491138632251)
        ·
          refine ⟨81050276592417736707948377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54033517728278491138632251 81050276592417736707948377)
          ·
            refine ⟨60787707444313302530961283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81050276592417736707948377 60787707444313302530961283)
            ·
              refine ⟨91181561166469953796441925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60787707444313302530961283 91181561166469953796441925)
              ·
                refine ⟨17096542718713116336832861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91181561166469953796441925 17096542718713116336832861)
                ·
                  refine ⟨6411203519517418626312323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17096542718713116336832861 6411203519517418626312323)
                  ·
                    refine ⟨9616805279276127939468485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6411203519517418626312323 9616805279276127939468485)
                    ·
                      refine ⟨1803150989864273988650341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9616805279276127939468485 1803150989864273988650341)
                      ·
                        rfl

theorem cell23_3511624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3511624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511624 prefixEnd_3511624 := by exact prefixLift 3511624
  have htrace : WordTrace (prefixWord ++ tailWord_3511624) baseStart_3511624 baseEnd_3511624 := by
    simpa [prefixWord, tailWord_3511624, baseEnd_3511624] using wordTrace_append hprefix tailTrace_3511624
  have hstable : (prefixWord ++ tailWord_3511624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511624).length < 2 ^ (prefixWord ++ tailWord_3511624).sum := by decide
  have hdescent : baseEnd_3511624 < baseStart_3511624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511627 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_3511627 : Nat := 118140960795 + 3511627 * 2 ^ 59
def prefixEnd_3511627 : Nat := 4983230072969 + 3 ^ 40 * 3511627 * 2
def baseEnd_3511627 : Nat := 1803152530306237476912827

theorem tailTrace_3511627 : CollatzResearch.WordTrace tailWord_3511627 prefixEnd_3511627 1803152530306237476912827 := by
  unfold tailWord_3511627
  simp only [CollatzResearch.WordTrace]
  refine ⟨128079558848982591989117135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85386372565988394659411423 128079558848982591989117135)
  ·
    refine ⟨192119338273473887983675703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128079558848982591989117135 192119338273473887983675703)
    ·
      refine ⟨288179007410210831975513555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192119338273473887983675703 288179007410210831975513555)
      ·
        refine ⟨432268511115316247963270333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288179007410210831975513555 432268511115316247963270333)
        ·
          refine ⟨162100691668243592986226375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432268511115316247963270333 162100691668243592986226375)
          ·
            refine ⟨243151037502365389479339563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162100691668243592986226375 243151037502365389479339563)
            ·
              refine ⟨364726556253548084219009345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243151037502365389479339563 364726556253548084219009345)
              ·
                refine ⟨273544917190161063164257009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364726556253548084219009345 273544917190161063164257009)
                ·
                  refine ⟨205158687892620797373192757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273544917190161063164257009 205158687892620797373192757)
                  ·
                    refine ⟨19233626989933199753736821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 205158687892620797373192757 19233626989933199753736821)
                    ·
                      refine ⟨1803152530306237476912827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19233626989933199753736821 1803152530306237476912827)
                      ·
                        rfl

theorem cell23_3511627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_3511627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511627 prefixEnd_3511627 := by exact prefixLift 3511627
  have htrace : WordTrace (prefixWord ++ tailWord_3511627) baseStart_3511627 baseEnd_3511627 := by
    simpa [prefixWord, tailWord_3511627, baseEnd_3511627] using wordTrace_append hprefix tailTrace_3511627
  have hstable : (prefixWord ++ tailWord_3511627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511627).length < 2 ^ (prefixWord ++ tailWord_3511627).sum := by decide
  have hdescent : baseEnd_3511627 < baseStart_3511627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511634 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3511634 : Nat := 118140960795 + 3511634 * 2 ^ 59
def prefixEnd_3511634 : Nat := 4983230072969 + 3 ^ 40 * 3511634 * 2
def baseEnd_3511634 : Nat := 601052041556939649841765

theorem tailTrace_3511634 : CollatzResearch.WordTrace tailWord_3511634 prefixEnd_3511634 601052041556939649841765 := by
  unfold tailWord_3511634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32019953539989308046155489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85386542773304821456414637 32019953539989308046155489)
  ·
    refine ⟨24014965154991981034616617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32019953539989308046155489 24014965154991981034616617)
    ·
      refine ⟨18011223866243985775962463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24014965154991981034616617 18011223866243985775962463)
      ·
        refine ⟨27016835799365978663943695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18011223866243985775962463 27016835799365978663943695)
        ·
          refine ⟨40525253699048967995915543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27016835799365978663943695 40525253699048967995915543)
          ·
            refine ⟨60787880548573451993873315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40525253699048967995915543 60787880548573451993873315)
            ·
              refine ⟨91181820822860177990809973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60787880548573451993873315 91181820822860177990809973)
              ·
                refine ⟨8548295702143141686638435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91181820822860177990809973 8548295702143141686638435)
                ·
                  refine ⟨12822443553214712529957653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548295702143141686638435 12822443553214712529957653)
                  ·
                    refine ⟨601052041556939649841765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12822443553214712529957653 601052041556939649841765)
                    ·
                      rfl

theorem cell23_3511634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3511634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511634 prefixEnd_3511634 := by exact prefixLift 3511634
  have htrace : WordTrace (prefixWord ++ tailWord_3511634) baseStart_3511634 baseEnd_3511634 := by
    simpa [prefixWord, tailWord_3511634, baseEnd_3511634] using wordTrace_append hprefix tailTrace_3511634
  have hstable : (prefixWord ++ tailWord_3511634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511634).length < 2 ^ (prefixWord ++ tailWord_3511634).sum := by decide
  have hdescent : baseEnd_3511634 < baseStart_3511634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511641 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_3511641 : Nat := 118140960795 + 3511641 * 2 ^ 59
def prefixEnd_3511641 : Nat := 4983230072969 + 3 ^ 40 * 3511641 * 2
def baseEnd_3511641 : Nat := 1803159719035400422137763

theorem tailTrace_3511641 : CollatzResearch.WordTrace tailWord_3511641 prefixEnd_3511641 1803159719035400422137763 := by
  unfold tailWord_3511641
  simp only [CollatzResearch.WordTrace]
  refine ⟨128080069470931872380126777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85386712980621248253417851 128080069470931872380126777)
  ·
    refine ⟨96060052103198904285095083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128080069470931872380126777 96060052103198904285095083)
    ·
      refine ⟨144090078154798356427642625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96060052103198904285095083 144090078154798356427642625)
      ·
        refine ⟨108067558616098767320731969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144090078154798356427642625 108067558616098767320731969)
        ·
          refine ⟨81050668962074075490548977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108067558616098767320731969 81050668962074075490548977)
          ·
            refine ⟨60788001721555556617911733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81050668962074075490548977 60788001721555556617911733)
            ·
              refine ⟨5698875161395833432929225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60788001721555556617911733 5698875161395833432929225)
              ·
                refine ⟨4274156371046875074696919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5698875161395833432929225 4274156371046875074696919)
                ·
                  refine ⟨6411234556570312612045379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274156371046875074696919 6411234556570312612045379)
                  ·
                    refine ⟨9616851834855468918068069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6411234556570312612045379 9616851834855468918068069)
                    ·
                      refine ⟨1803159719035400422137763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9616851834855468918068069 1803159719035400422137763)
                      ·
                        rfl

theorem cell23_3511641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_3511641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511641 prefixEnd_3511641 := by exact prefixLift 3511641
  have htrace : WordTrace (prefixWord ++ tailWord_3511641) baseStart_3511641 baseEnd_3511641 := by
    simpa [prefixWord, tailWord_3511641, baseEnd_3511641] using wordTrace_append hprefix tailTrace_3511641
  have hstable : (prefixWord ++ tailWord_3511641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511641).length < 2 ^ (prefixWord ++ tailWord_3511641).sum := by decide
  have hdescent : baseEnd_3511641 < baseStart_3511641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511661 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3511661 : Nat := 118140960795 + 3511661 * 2 ^ 59
def prefixEnd_3511661 : Nat := 4983230072969 + 3 ^ 40 * 3511661 * 2
def baseEnd_3511661 : Nat := 1803169988648490343887671

theorem tailTrace_3511661 : CollatzResearch.WordTrace tailWord_3511661 prefixEnd_3511661 1803169988648490343887671 := by
  unfold tailWord_3511661
  simp only [CollatzResearch.WordTrace]
  refine ⟨128080798930859415795854837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85387199287239610530569891 128080798930859415795854837)
  ·
    refine ⟨12007574899768070230861391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128080798930859415795854837 12007574899768070230861391)
    ·
      refine ⟨18011362349652105346292087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12007574899768070230861391 18011362349652105346292087)
      ·
        refine ⟨27017043524478158019438131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18011362349652105346292087 27017043524478158019438131)
        ·
          refine ⟨40525565286717237029157197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27017043524478158019438131 40525565286717237029157197)
          ·
            refine ⟨15197086982518963885933949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40525565286717237029157197 15197086982518963885933949)
            ·
              refine ⟨5698907618444611457225231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15197086982518963885933949 5698907618444611457225231)
              ·
                refine ⟨8548361427666917185837847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698907618444611457225231 8548361427666917185837847)
                ·
                  refine ⟨12822542141500375778756771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548361427666917185837847 12822542141500375778756771)
                  ·
                    refine ⟨19233813212250563668135157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12822542141500375778756771 19233813212250563668135157)
                    ·
                      refine ⟨1803169988648490343887671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19233813212250563668135157 1803169988648490343887671)
                      ·
                        rfl

theorem cell23_3511661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3511661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511661 prefixEnd_3511661 := by exact prefixLift 3511661
  have htrace : WordTrace (prefixWord ++ tailWord_3511661) baseStart_3511661 baseEnd_3511661 := by
    simpa [prefixWord, tailWord_3511661, baseEnd_3511661] using wordTrace_append hprefix tailTrace_3511661
  have hstable : (prefixWord ++ tailWord_3511661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511661).length < 2 ^ (prefixWord ++ tailWord_3511661).sum := by decide
  have hdescent : baseEnd_3511661 < baseStart_3511661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511669 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3511669 : Nat := 118140960795 + 3511669 * 2 ^ 59
def prefixEnd_3511669 : Nat := 4983230072969 + 3 ^ 40 * 3511669 * 2
def baseEnd_3511669 : Nat := 1803174096493726312587635

theorem tailTrace_3511669 : CollatzResearch.WordTrace tailWord_3511669 prefixEnd_3511669 1803174096493726312587635 := by
  unfold tailWord_3511669
  simp only [CollatzResearch.WordTrace]
  refine ⟨128081090714830433162146061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85387393809886955441430707 128081090714830433162146061)
  ·
    refine ⟨48030409018061412435804773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128081090714830433162146061 48030409018061412435804773)
    ·
      refine ⟨9005701690886514831713395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48030409018061412435804773 9005701690886514831713395)
      ·
        refine ⟨13508552536329772247570093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9005701690886514831713395 13508552536329772247570093)
        ·
          refine ⟨5065707201123664592838785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13508552536329772247570093 5065707201123664592838785)
          ·
            refine ⟨3799280400842748444629089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065707201123664592838785 3799280400842748444629089)
            ·
              refine ⟨2849460300632061333471817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799280400842748444629089 2849460300632061333471817)
              ·
                refine ⟨2137095225474046000103863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849460300632061333471817 2137095225474046000103863)
                ·
                  refine ⟨3205642838211069000155795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137095225474046000103863 3205642838211069000155795)
                  ·
                    refine ⟨4808464257316603500233693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3205642838211069000155795 4808464257316603500233693)
                    ·
                      refine ⟨1803174096493726312587635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4808464257316603500233693 1803174096493726312587635)
                      ·
                        rfl

theorem cell23_3511669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3511669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511669 prefixEnd_3511669 := by exact prefixLift 3511669
  have htrace : WordTrace (prefixWord ++ tailWord_3511669) baseStart_3511669 baseEnd_3511669 := by
    simpa [prefixWord, tailWord_3511669, baseEnd_3511669] using wordTrace_append hprefix tailTrace_3511669
  have hstable : (prefixWord ++ tailWord_3511669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511669).length < 2 ^ (prefixWord ++ tailWord_3511669).sum := by decide
  have hdescent : baseEnd_3511669 < baseStart_3511669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3511675 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 1, 2, 2]
def baseStart_3511675 : Nat := 118140960795 + 3511675 * 2 ^ 59
def prefixEnd_3511675 : Nat := 4983230072969 + 3 ^ 40 * 3511675 * 2
def baseEnd_3511675 : Nat := 1803177177377653289112607

theorem tailTrace_3511675 : CollatzResearch.WordTrace tailWord_3511675 prefixEnd_3511675 1803177177377653289112607 := by
  unfold tailWord_3511675
  simp only [CollatzResearch.WordTrace]
  refine ⟨128081309552808696186864479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85387539701872464124576319 128081309552808696186864479)
  ·
    refine ⟨192121964329213044280296719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128081309552808696186864479 192121964329213044280296719)
    ·
      refine ⟨288182946493819566420445079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192121964329213044280296719 288182946493819566420445079)
      ·
        refine ⟨432274419740729349630667619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288182946493819566420445079 432274419740729349630667619)
        ·
          refine ⟨648411629611094024446001429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432274419740729349630667619 648411629611094024446001429)
          ·
            refine ⟨30394295138020032395906317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 648411629611094024446001429 30394295138020032395906317)
            ·
              refine ⟨11397860676757512148464869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30394295138020032395906317 11397860676757512148464869)
              ·
                refine ⟨2137098876892033527837163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11397860676757512148464869 2137098876892033527837163)
                ·
                  refine ⟨3205648315338050291755745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137098876892033527837163 3205648315338050291755745)
                  ·
                    refine ⟨2404236236503537718816809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205648315338050291755745 2404236236503537718816809)
                    ·
                      refine ⟨1803177177377653289112607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2404236236503537718816809 1803177177377653289112607)
                      ·
                        rfl

theorem cell23_3511675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 2, 2].length) (baseStart_3511675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3511675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3511675 prefixEnd_3511675 := by exact prefixLift 3511675
  have htrace : WordTrace (prefixWord ++ tailWord_3511675) baseStart_3511675 baseEnd_3511675 := by
    simpa [prefixWord, tailWord_3511675, baseEnd_3511675] using wordTrace_append hprefix tailTrace_3511675
  have hstable : (prefixWord ++ tailWord_3511675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3511675).length < 2 ^ (prefixWord ++ tailWord_3511675).sum := by decide
  have hdescent : baseEnd_3511675 < baseStart_3511675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3511675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
