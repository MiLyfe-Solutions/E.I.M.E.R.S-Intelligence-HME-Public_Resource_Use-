import V185TrunkScan23Chunk1062

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6292438 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6292438 : Nat := 118140960795 + 6292438 * 2 ^ 59
def prefixEnd_6292438 : Nat := 4983230072969 + 3 ^ 40 * 6292438 * 2
def baseEnd_6292438 : Nat := 3231045182616157041086611

theorem tailTrace_6292438 : CollatzResearch.WordTrace tailWord_6292438 prefixEnd_6292438 3231045182616157041086611 := by
  unfold tailWord_6292438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14344004273598703981076873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153002712251719509131486645 14344004273598703981076873)
  ·
    refine ⟨10758003205199027985807655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14344004273598703981076873 10758003205199027985807655)
    ·
      refine ⟨16137004807798541978711483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10758003205199027985807655 16137004807798541978711483)
      ·
        refine ⟨24205507211697812968067225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16137004807798541978711483 24205507211697812968067225)
        ·
          refine ⟨18154130408773359726050419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24205507211697812968067225 18154130408773359726050419)
          ·
            refine ⟨27231195613160039589075629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18154130408773359726050419 27231195613160039589075629)
            ·
              refine ⟨10211698354935014845903361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27231195613160039589075629 10211698354935014845903361)
              ·
                refine ⟨7658773766201261134427521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10211698354935014845903361 7658773766201261134427521)
                ·
                  refine ⟨5744080324650945850820641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658773766201261134427521 5744080324650945850820641)
                  ·
                    refine ⟨4308060243488209388115481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744080324650945850820641 4308060243488209388115481)
                    ·
                      refine ⟨3231045182616157041086611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308060243488209388115481 3231045182616157041086611)
                      ·
                        rfl

theorem cell23_6292438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6292438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292438 prefixEnd_6292438 := by exact prefixLift 6292438
  have htrace : WordTrace (prefixWord ++ tailWord_6292438) baseStart_6292438 baseEnd_6292438 := by
    simpa [prefixWord, tailWord_6292438, baseEnd_6292438] using wordTrace_append hprefix tailTrace_6292438
  have hstable : (prefixWord ++ tailWord_6292438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292438).length < 2 ^ (prefixWord ++ tailWord_6292438).sum := by decide
  have hdescent : baseEnd_6292438 < baseStart_6292438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292478 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_6292478 : Nat := 118140960795 + 6292478 * 2 ^ 59
def prefixEnd_6292478 : Nat := 4983230072969 + 3 ^ 40 * 6292478 * 2
def baseEnd_6292478 : Nat := 359007302426926320509603

theorem tailTrace_6292478 : CollatzResearch.WordTrace tailWord_6292478 prefixEnd_6292478 359007302426926320509603 := by
  unfold tailWord_6292478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28688190912179293816085761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153003684864956233685790725 28688190912179293816085761)
  ·
    refine ⟨21516143184134470362064321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28688190912179293816085761 21516143184134470362064321)
    ·
      refine ⟨16137107388100852771548241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21516143184134470362064321 16137107388100852771548241)
      ·
        refine ⟨12102830541075639578661181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16137107388100852771548241 12102830541075639578661181)
        ·
          refine ⟨4538561452903364841997943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12102830541075639578661181 4538561452903364841997943)
          ·
            refine ⟨6807842179355047262996915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538561452903364841997943 6807842179355047262996915)
            ·
              refine ⟨10211763269032570894495373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807842179355047262996915 10211763269032570894495373)
              ·
                refine ⟨3829411225887214085435765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10211763269032570894495373 3829411225887214085435765)
                ·
                  refine ⟨359007302426926320509603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3829411225887214085435765 359007302426926320509603)
                  ·
                    rfl

theorem cell23_6292478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_6292478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292478 prefixEnd_6292478 := by exact prefixLift 6292478
  have htrace : WordTrace (prefixWord ++ tailWord_6292478) baseStart_6292478 baseEnd_6292478 := by
    simpa [prefixWord, tailWord_6292478, baseEnd_6292478] using wordTrace_append hprefix tailTrace_6292478
  have hstable : (prefixWord ++ tailWord_6292478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292478).length < 2 ^ (prefixWord ++ tailWord_6292478).sum := by decide
  have hdescent : baseEnd_6292478 < baseStart_6292478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292504 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_6292504 : Nat := 118140960795 + 6292504 * 2 ^ 59
def prefixEnd_6292504 : Nat := 4983230072969 + 3 ^ 40 * 6292504 * 2
def baseEnd_6292504 : Nat := 1077026357446451260953769

theorem tailTrace_6292504 : CollatzResearch.WordTrace tailWord_6292504 prefixEnd_6292504 1077026357446451260953769 := by
  unfold tailWord_6292504
  simp only [CollatzResearch.WordTrace]
  refine ⟨114753237797670078484566283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153004317063560104646088377 114753237797670078484566283)
  ·
    refine ⟨172129856696505117726849425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114753237797670078484566283 172129856696505117726849425)
    ·
      refine ⟨129097392522378838295137069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172129856696505117726849425 129097392522378838295137069)
      ·
        refine ⟨48411522195892064360676401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129097392522378838295137069 48411522195892064360676401)
        ·
          refine ⟨36308641646919048270507301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48411522195892064360676401 36308641646919048270507301)
          ·
            refine ⟨6807870308797321550720119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36308641646919048270507301 6807870308797321550720119)
            ·
              refine ⟨10211805463195982326080179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807870308797321550720119 10211805463195982326080179)
              ·
                refine ⟨15317708194793973489120269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10211805463195982326080179 15317708194793973489120269)
                ·
                  refine ⟨5744140573047740058420101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15317708194793973489120269 5744140573047740058420101)
                  ·
                    refine ⟨1077026357446451260953769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744140573047740058420101 1077026357446451260953769)
                    ·
                      rfl

theorem cell23_6292504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_6292504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292504 prefixEnd_6292504 := by exact prefixLift 6292504
  have htrace : WordTrace (prefixWord ++ tailWord_6292504) baseStart_6292504 baseEnd_6292504 := by
    simpa [prefixWord, tailWord_6292504, baseEnd_6292504] using wordTrace_append hprefix tailTrace_6292504
  have hstable : (prefixWord ++ tailWord_6292504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292504).length < 2 ^ (prefixWord ++ tailWord_6292504).sum := by decide
  have hdescent : baseEnd_6292504 < baseStart_6292504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292554 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_6292554 : Nat := 118140960795 + 6292554 * 2 ^ 59
def prefixEnd_6292554 : Nat := 4983230072969 + 3 ^ 40 * 6292554 * 2
def baseEnd_6292554 : Nat := 3231104746372078587236077

theorem tailTrace_6292554 : CollatzResearch.WordTrace tailWord_6292554 prefixEnd_6292554 3231104746372078587236077 := by
  unfold tailWord_6292554
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377074811289753877113179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153005532830106010338968477 57377074811289753877113179)
  ·
    refine ⟨86065612216934630815669769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57377074811289753877113179 86065612216934630815669769)
    ·
      refine ⟨64549209162700973111752327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86065612216934630815669769 64549209162700973111752327)
      ·
        refine ⟨96823813744051459667628491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64549209162700973111752327 96823813744051459667628491)
        ·
          refine ⟨145235720616077189501442737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96823813744051459667628491 145235720616077189501442737)
          ·
            refine ⟨108926790462057892126082053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145235720616077189501442737 108926790462057892126082053)
            ·
              refine ⟨20423773211635854773640385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108926790462057892126082053 20423773211635854773640385)
              ·
                refine ⟨15317829908726891080230289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20423773211635854773640385 15317829908726891080230289)
                ·
                  refine ⟨11488372431545168310172717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15317829908726891080230289 11488372431545168310172717)
                  ·
                    refine ⟨4308139661829438116314769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11488372431545168310172717 4308139661829438116314769)
                    ·
                      refine ⟨3231104746372078587236077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308139661829438116314769 3231104746372078587236077)
                      ·
                        rfl

theorem cell23_6292554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_6292554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292554 prefixEnd_6292554 := by exact prefixLift 6292554
  have htrace : WordTrace (prefixWord ++ tailWord_6292554) baseStart_6292554 baseEnd_6292554 := by
    simpa [prefixWord, tailWord_6292554, baseEnd_6292554] using wordTrace_append hprefix tailTrace_6292554
  have hstable : (prefixWord ++ tailWord_6292554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292554).length < 2 ^ (prefixWord ++ tailWord_6292554).sum := by decide
  have hdescent : baseEnd_6292554 < baseStart_6292554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292567 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_6292567 : Nat := 118140960795 + 6292567 * 2 ^ 59
def prefixEnd_6292567 : Nat := 4983230072969 + 3 ^ 40 * 6292567 * 2
def baseEnd_6292567 : Nat := 3231111421620587036373517

theorem tailTrace_6292567 : CollatzResearch.WordTrace tailWord_6292567 prefixEnd_6292567 3231111421620587036373517 := by
  unfold tailWord_6292567
  simp only [CollatzResearch.WordTrace]
  refine ⟨229508773394111918728675955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153005848929407945819117303 229508773394111918728675955)
  ·
    refine ⟨344263160091167878093013933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229508773394111918728675955 344263160091167878093013933)
    ·
      refine ⟨129098685034187954284880225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344263160091167878093013933 129098685034187954284880225)
      ·
        refine ⟨96824013775640965713660169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129098685034187954284880225 96824013775640965713660169)
        ·
          refine ⟨72618010331730724285245127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96824013775640965713660169 72618010331730724285245127)
          ·
            refine ⟨108927015497596086427867691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72618010331730724285245127 108927015497596086427867691)
            ·
              refine ⟨163390523246394129641801537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108927015497596086427867691 163390523246394129641801537)
              ·
                refine ⟨122542892434795597231351153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163390523246394129641801537 122542892434795597231351153)
                ·
                  refine ⟨91907169326096697923513365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122542892434795597231351153 91907169326096697923513365)
                  ·
                    refine ⟨4308148562160782715164689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91907169326096697923513365 4308148562160782715164689)
                    ·
                      refine ⟨3231111421620587036373517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308148562160782715164689 3231111421620587036373517)
                      ·
                        rfl

theorem cell23_6292567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_6292567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292567 prefixEnd_6292567 := by exact prefixLift 6292567
  have htrace : WordTrace (prefixWord ++ tailWord_6292567) baseStart_6292567 baseEnd_6292567 := by
    simpa [prefixWord, tailWord_6292567, baseEnd_6292567] using wordTrace_append hprefix tailTrace_6292567
  have hstable : (prefixWord ++ tailWord_6292567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292567).length < 2 ^ (prefixWord ++ tailWord_6292567).sum := by decide
  have hdescent : baseEnd_6292567 < baseStart_6292567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292604 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_6292604 : Nat := 118140960795 + 6292604 * 2 ^ 59
def prefixEnd_6292604 : Nat := 4983230072969 + 3 ^ 40 * 6292604 * 2
def baseEnd_6292604 : Nat := 3231130420404803391610847

theorem tailTrace_6292604 : CollatzResearch.WordTrace tailWord_6292604 prefixEnd_6292604 3231130420404803391610847 := by
  unfold tailWord_6292604
  simp only [CollatzResearch.WordTrace]
  refine ⟨114755061447488937023886433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153006748596651916031848577 114755061447488937023886433)
  ·
    refine ⟨86066296085616702767914825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114755061447488937023886433 86066296085616702767914825)
    ·
      refine ⟨64549722064212527075936119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86066296085616702767914825 64549722064212527075936119)
      ·
        refine ⟨96824583096318790613904179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64549722064212527075936119 96824583096318790613904179)
        ·
          refine ⟨145236874644478185920856269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96824583096318790613904179 145236874644478185920856269)
          ·
            refine ⟨54463827991679319720321101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145236874644478185920856269 54463827991679319720321101)
            ·
              refine ⟨20423935496879744895120413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54463827991679319720321101 20423935496879744895120413)
              ·
                refine ⟨7658975811329904335670155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20423935496879744895120413 7658975811329904335670155)
                ·
                  refine ⟨11488463716994856503505233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658975811329904335670155 11488463716994856503505233)
                  ·
                    refine ⟨8616347787746142377628925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11488463716994856503505233 8616347787746142377628925)
                    ·
                      refine ⟨3231130420404803391610847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616347787746142377628925 3231130420404803391610847)
                      ·
                        rfl

theorem cell23_6292604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_6292604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292604 prefixEnd_6292604 := by exact prefixLift 6292604
  have htrace : WordTrace (prefixWord ++ tailWord_6292604) baseStart_6292604 baseEnd_6292604 := by
    simpa [prefixWord, tailWord_6292604, baseEnd_6292604] using wordTrace_append hprefix tailTrace_6292604
  have hstable : (prefixWord ++ tailWord_6292604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292604).length < 2 ^ (prefixWord ++ tailWord_6292604).sum := by decide
  have hdescent : baseEnd_6292604 < baseStart_6292604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292618 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_6292618 : Nat := 118140960795 + 6292618 * 2 ^ 59
def prefixEnd_6292618 : Nat := 4983230072969 + 3 ^ 40 * 6292618 * 2
def baseEnd_6292618 : Nat := 3231137609133966336835783

theorem tailTrace_6292618 : CollatzResearch.WordTrace tailWord_6292618 prefixEnd_6292618 3231137609133966336835783 := by
  unfold tailWord_6292618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377658379231788609695627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153007089011284769625855005 57377658379231788609695627)
  ·
    refine ⟨86066487568847682914543441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57377658379231788609695627 86066487568847682914543441)
    ·
      refine ⟨64549865676635762185907581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86066487568847682914543441 64549865676635762185907581)
      ·
        refine ⟨24206199628738410819715343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64549865676635762185907581 24206199628738410819715343)
        ·
          refine ⟨36309299443107616229573015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24206199628738410819715343 36309299443107616229573015)
          ·
            refine ⟨54463949164661424344359523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36309299443107616229573015 54463949164661424344359523)
            ·
              refine ⟨81695923746992136516539285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54463949164661424344359523 81695923746992136516539285)
              ·
                refine ⟨3829496425640256399212779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81695923746992136516539285 3829496425640256399212779)
                ·
                  refine ⟨5744244638460384598819169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829496425640256399212779 5744244638460384598819169)
                  ·
                    refine ⟨4308183478845288449114377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744244638460384598819169 4308183478845288449114377)
                    ·
                      refine ⟨3231137609133966336835783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308183478845288449114377 3231137609133966336835783)
                      ·
                        rfl

theorem cell23_6292618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_6292618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292618 prefixEnd_6292618 := by exact prefixLift 6292618
  have htrace : WordTrace (prefixWord ++ tailWord_6292618) baseStart_6292618 baseEnd_6292618 := by
    simpa [prefixWord, tailWord_6292618, baseEnd_6292618] using wordTrace_append hprefix tailTrace_6292618
  have hstable : (prefixWord ++ tailWord_6292618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292618).length < 2 ^ (prefixWord ++ tailWord_6292618).sum := by decide
  have hdescent : baseEnd_6292618 < baseStart_6292618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292620 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_6292620 : Nat := 118140960795 + 6292620 * 2 ^ 59
def prefixEnd_6292620 : Nat := 4983230072969 + 3 ^ 40 * 6292620 * 2
def baseEnd_6292620 : Nat := 1077046212031758443003591

theorem tailTrace_6292620 : CollatzResearch.WordTrace tailWord_6292620 prefixEnd_6292620 1077046212031758443003591 := by
  unfold tailWord_6292620
  simp only [CollatzResearch.WordTrace]
  refine ⟨114755353231459954390177657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153007137641946605853570209 114755353231459954390177657)
  ·
    refine ⟨86066514923594965792633243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114755353231459954390177657 86066514923594965792633243)
    ·
      refine ⟨129099772385392448688949865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86066514923594965792633243 129099772385392448688949865)
      ·
        refine ⟨96824829289044336516712399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129099772385392448688949865 96824829289044336516712399)
        ·
          refine ⟨145237243933566504775068599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96824829289044336516712399 145237243933566504775068599)
          ·
            refine ⟨217855865900349757162602899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145237243933566504775068599 217855865900349757162602899)
            ·
              refine ⟨326783798850524635743904349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217855865900349757162602899 326783798850524635743904349)
              ·
                refine ⟨122543924568946738403964131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326783798850524635743904349 122543924568946738403964131)
                ·
                  refine ⟨183815886853420107605946197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122543924568946738403964131 183815886853420107605946197)
                  ·
                    refine ⟨1077046212031758443003591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183815886853420107605946197 1077046212031758443003591)
                    ·
                      rfl

theorem cell23_6292620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_6292620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292620 prefixEnd_6292620 := by exact prefixLift 6292620
  have htrace : WordTrace (prefixWord ++ tailWord_6292620) baseStart_6292620 baseEnd_6292620 := by
    simpa [prefixWord, tailWord_6292620, baseEnd_6292620] using wordTrace_append hprefix tailTrace_6292620
  have hstable : (prefixWord ++ tailWord_6292620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292620).length < 2 ^ (prefixWord ++ tailWord_6292620).sum := by decide
  have hdescent : baseEnd_6292620 < baseStart_6292620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292638 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_6292638 : Nat := 118140960795 + 6292638 * 2 ^ 59
def prefixEnd_6292638 : Nat := 4983230072969 + 3 ^ 40 * 6292638 * 2
def baseEnd_6292638 : Nat := 3231147878747056258585691

theorem tailTrace_6292638 : CollatzResearch.WordTrace tailWord_6292638 prefixEnd_6292638 3231147878747056258585691 := by
  unfold tailWord_6292638
  simp only [CollatzResearch.WordTrace]
  refine ⟨28688920372106837231813821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153007575317903131903007045 28688920372106837231813821)
  ·
    refine ⟨10758345139540063961930183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28688920372106837231813821 10758345139540063961930183)
    ·
      refine ⟨16137517709310095942895275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10758345139540063961930183 16137517709310095942895275)
      ·
        refine ⟨24206276563965143914342913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16137517709310095942895275 24206276563965143914342913)
        ·
          refine ⟨18154707422973857935757185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24206276563965143914342913 18154707422973857935757185)
          ·
            refine ⟨13616030567230393451817889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18154707422973857935757185 13616030567230393451817889)
            ·
              refine ⟨10212022925422795088863417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13616030567230393451817889 10212022925422795088863417)
              ·
                refine ⟨7659017194067096316647563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212022925422795088863417 7659017194067096316647563)
                ·
                  refine ⟨11488525791100644474971345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659017194067096316647563 11488525791100644474971345)
                  ·
                    refine ⟨8616394343325483356228509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11488525791100644474971345 8616394343325483356228509)
                    ·
                      refine ⟨3231147878747056258585691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616394343325483356228509 3231147878747056258585691)
                      ·
                        rfl

theorem cell23_6292638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_6292638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292638 prefixEnd_6292638 := by exact prefixLift 6292638
  have htrace : WordTrace (prefixWord ++ tailWord_6292638) baseStart_6292638 baseEnd_6292638 := by
    simpa [prefixWord, tailWord_6292638, baseEnd_6292638] using wordTrace_append hprefix tailTrace_6292638
  have hstable : (prefixWord ++ tailWord_6292638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292638).length < 2 ^ (prefixWord ++ tailWord_6292638).sum := by decide
  have hdescent : baseEnd_6292638 < baseStart_6292638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292677 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_6292677 : Nat := 118140960795 + 6292677 * 2 ^ 59
def prefixEnd_6292677 : Nat := 4983230072969 + 3 ^ 40 * 6292677 * 2
def baseEnd_6292677 : Nat := 3231167904492581605998011

theorem tailTrace_6292677 : CollatzResearch.WordTrace tailWord_6292677 prefixEnd_6292677 3231167904492581605998011 := by
  unfold tailWord_6292677
  simp only [CollatzResearch.WordTrace]
  refine ⟨229512785423713407515180285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153008523615808938343453523 229512785423713407515180285)
  ·
    refine ⟨86067294533892527818192607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229512785423713407515180285 86067294533892527818192607)
    ·
      refine ⟨129100941800838791727288911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86067294533892527818192607 129100941800838791727288911)
      ·
        refine ⟨193651412701258187590933367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129100941800838791727288911 193651412701258187590933367)
        ·
          refine ⟨290477119051887281386400051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193651412701258187590933367 290477119051887281386400051)
          ·
            refine ⟨435715678577830922079600077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290477119051887281386400051 435715678577830922079600077)
            ·
              refine ⟨163393379466686595779850029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435715678577830922079600077 163393379466686595779850029)
              ·
                refine ⟨61272517300007473417443761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163393379466686595779850029 61272517300007473417443761)
                ·
                  refine ⟨45954387975005605063082821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61272517300007473417443761 45954387975005605063082821)
                  ·
                    refine ⟨8616447745313550949328029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45954387975005605063082821 8616447745313550949328029)
                    ·
                      refine ⟨3231167904492581605998011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616447745313550949328029 3231167904492581605998011)
                      ·
                        rfl

theorem cell23_6292677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_6292677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292677 prefixEnd_6292677 := by exact prefixLift 6292677
  have htrace : WordTrace (prefixWord ++ tailWord_6292677) baseStart_6292677 baseEnd_6292677 := by
    simpa [prefixWord, tailWord_6292677, baseEnd_6292677] using wordTrace_append hprefix tailTrace_6292677
  have hstable : (prefixWord ++ tailWord_6292677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292677).length < 2 ^ (prefixWord ++ tailWord_6292677).sum := by decide
  have hdescent : baseEnd_6292677 < baseStart_6292677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292691 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 2, 2, 2]
def baseStart_6292691 : Nat := 118140960795 + 6292691 * 2 ^ 59
def prefixEnd_6292691 : Nat := 4983230072969 + 3 ^ 40 * 6292691 * 2
def baseEnd_6292691 : Nat := 3231175093221744551222947

theorem tailTrace_6292691 : CollatzResearch.WordTrace tailWord_6292691 prefixEnd_6292691 3231175093221744551222947 := by
  unfold tailWord_6292691
  simp only [CollatzResearch.WordTrace]
  refine ⟨229513296045662687906189927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153008864030441791937459951 229513296045662687906189927)
  ·
    refine ⟨344269944068494031859284891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229513296045662687906189927 344269944068494031859284891)
    ·
      refine ⟨516404916102741047788927337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344269944068494031859284891 516404916102741047788927337)
      ·
        refine ⟨387303687077055785841695503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516404916102741047788927337 387303687077055785841695503)
        ·
          refine ⟨580955530615583678762543255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387303687077055785841695503 580955530615583678762543255)
          ·
            refine ⟨871433295923375518143814883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580955530615583678762543255 871433295923375518143814883)
            ·
              refine ⟨1307149943885063277215722325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871433295923375518143814883 1307149943885063277215722325)
              ·
                refine ⟨7659081702451542639935873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1307149943885063277215722325 7659081702451542639935873)
                ·
                  refine ⟨5744311276838656979951905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7659081702451542639935873 5744311276838656979951905)
                  ·
                    refine ⟨4308233457628992734963929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744311276838656979951905 4308233457628992734963929)
                    ·
                      refine ⟨3231175093221744551222947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308233457628992734963929 3231175093221744551222947)
                      ·
                        rfl

theorem cell23_6292691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 2, 2].length) (baseStart_6292691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292691 prefixEnd_6292691 := by exact prefixLift 6292691
  have htrace : WordTrace (prefixWord ++ tailWord_6292691) baseStart_6292691 baseEnd_6292691 := by
    simpa [prefixWord, tailWord_6292691, baseEnd_6292691] using wordTrace_append hprefix tailTrace_6292691
  have hstable : (prefixWord ++ tailWord_6292691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292691).length < 2 ^ (prefixWord ++ tailWord_6292691).sum := by decide
  have hdescent : baseEnd_6292691 < baseStart_6292691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292784 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_6292784 : Nat := 118140960795 + 6292784 * 2 ^ 59
def prefixEnd_6292784 : Nat := 4983230072969 + 3 ^ 40 * 6292784 * 2
def baseEnd_6292784 : Nat := 3231222846922612687360019

theorem tailTrace_6292784 : CollatzResearch.WordTrace tailWord_6292784 prefixEnd_6292784 3231222846922612687360019 := by
  unfold tailWord_6292784
  simp only [CollatzResearch.WordTrace]
  refine ⟨114758344017162882394662703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153011125356217176526216937 114758344017162882394662703)
  ·
    refine ⟨172137516025744323591994055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114758344017162882394662703 172137516025744323591994055)
    ·
      refine ⟨258206274038616485387991083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172137516025744323591994055 258206274038616485387991083)
      ·
        refine ⟨387309411057924728081986625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258206274038616485387991083 387309411057924728081986625)
        ·
          refine ⟨290482058293443546061489969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387309411057924728081986625 290482058293443546061489969)
          ·
            refine ⟨217861543720082659546117477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290482058293443546061489969 217861543720082659546117477)
            ·
              refine ⟨40849039447515498664897027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217861543720082659546117477 40849039447515498664897027)
              ·
                refine ⟨61273559171273247997345541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40849039447515498664897027 61273559171273247997345541)
                ·
                  refine ⟨11488792344613733999502289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61273559171273247997345541 11488792344613733999502289)
                  ·
                    refine ⟨8616594258460300499626717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11488792344613733999502289 8616594258460300499626717)
                    ·
                      refine ⟨3231222846922612687360019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616594258460300499626717 3231222846922612687360019)
                      ·
                        rfl

theorem cell23_6292784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_6292784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292784 prefixEnd_6292784 := by exact prefixLift 6292784
  have htrace : WordTrace (prefixWord ++ tailWord_6292784) baseStart_6292784 baseEnd_6292784 := by
    simpa [prefixWord, tailWord_6292784, baseEnd_6292784] using wordTrace_append hprefix tailTrace_6292784
  have hstable : (prefixWord ++ tailWord_6292784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292784).length < 2 ^ (prefixWord ++ tailWord_6292784).sum := by decide
  have hdescent : baseEnd_6292784 < baseStart_6292784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292801 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6292801 : Nat := 118140960795 + 6292801 * 2 ^ 59
def prefixEnd_6292801 : Nat := 4983230072969 + 3 ^ 40 * 6292801 * 2
def baseEnd_6292801 : Nat := 3231231576093739120847441

theorem tailTrace_6292801 : CollatzResearch.WordTrace tailWord_6292801 prefixEnd_6292801 3231231576093739120847441 := by
  unfold tailWord_6292801
  simp only [CollatzResearch.WordTrace]
  refine ⟨229517308075264176692694257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153011538716842784461796171 229517308075264176692694257)
  ·
    refine ⟨172137981056448132519520693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229517308075264176692694257 172137981056448132519520693)
    ·
      refine ⟨16137935724042012423705065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172137981056448132519520693 16137935724042012423705065)
      ·
        refine ⟨12103451793031509317778799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16137935724042012423705065 12103451793031509317778799)
        ·
          refine ⟨18155177689547263976668199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12103451793031509317778799 18155177689547263976668199)
          ·
            refine ⟨27232766534320895965002299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18155177689547263976668199 27232766534320895965002299)
            ·
              refine ⟨40849149801481343947503449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27232766534320895965002299 40849149801481343947503449)
              ·
                refine ⟨30636862351111007960627587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40849149801481343947503449 30636862351111007960627587)
                ·
                  refine ⟨45955293526666511940941381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30636862351111007960627587 45955293526666511940941381)
                  ·
                    refine ⟨8616617536249970988926509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45955293526666511940941381 8616617536249970988926509)
                    ·
                      refine ⟨3231231576093739120847441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616617536249970988926509 3231231576093739120847441)
                      ·
                        rfl

theorem cell23_6292801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6292801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292801 prefixEnd_6292801 := by exact prefixLift 6292801
  have htrace : WordTrace (prefixWord ++ tailWord_6292801) baseStart_6292801 baseEnd_6292801 := by
    simpa [prefixWord, tailWord_6292801, baseEnd_6292801] using wordTrace_append hprefix tailTrace_6292801
  have hstable : (prefixWord ++ tailWord_6292801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292801).length < 2 ^ (prefixWord ++ tailWord_6292801).sum := by decide
  have hdescent : baseEnd_6292801 < baseStart_6292801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292814 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_6292814 : Nat := 118140960795 + 6292814 * 2 ^ 59
def prefixEnd_6292814 : Nat := 4983230072969 + 3 ^ 40 * 6292814 * 2
def baseEnd_6292814 : Nat := 3231238251342247569984881

theorem tailTrace_6292814 : CollatzResearch.WordTrace tailWord_6292814 prefixEnd_6292814 3231238251342247569984881 := by
  unfold tailWord_6292814
  simp only [CollatzResearch.WordTrace]
  refine ⟨28689722778027134989114687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153011854816144719941944997 28689722778027134989114687)
  ·
    refine ⟨43034584167040702483672031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28689722778027134989114687 43034584167040702483672031)
    ·
      refine ⟨64551876250561053725508047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43034584167040702483672031 64551876250561053725508047)
      ·
        refine ⟨96827814375841580588262071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64551876250561053725508047 96827814375841580588262071)
        ·
          refine ⟨145241721563762370882393107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96827814375841580588262071 145241721563762370882393107)
          ·
            refine ⟨217862582345643556323589661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145241721563762370882393107 217862582345643556323589661)
            ·
              refine ⟨81698468379616333621346123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217862582345643556323589661 81698468379616333621346123)
              ·
                refine ⟨122547702569424500432019185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81698468379616333621346123 122547702569424500432019185)
                ·
                  refine ⟨91910776927068375324014389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122547702569424500432019185 91910776927068375324014389)
                  ·
                    refine ⟨8616635336912660186626349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91910776927068375324014389 8616635336912660186626349)
                    ·
                      refine ⟨3231238251342247569984881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616635336912660186626349 3231238251342247569984881)
                      ·
                        rfl

theorem cell23_6292814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_6292814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292814 prefixEnd_6292814 := by exact prefixLift 6292814
  have htrace : WordTrace (prefixWord ++ tailWord_6292814) baseStart_6292814 baseEnd_6292814 := by
    simpa [prefixWord, tailWord_6292814, baseEnd_6292814] using wordTrace_append hprefix tailTrace_6292814
  have hstable : (prefixWord ++ tailWord_6292814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292814).length < 2 ^ (prefixWord ++ tailWord_6292814).sum := by decide
  have hdescent : baseEnd_6292814 < baseStart_6292814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292842 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_6292842 : Nat := 118140960795 + 6292842 * 2 ^ 59
def prefixEnd_6292842 : Nat := 4983230072969 + 3 ^ 40 * 6292842 * 2
def baseEnd_6292842 : Nat := 1077084209600191153478251

theorem tailTrace_6292842 : CollatzResearch.WordTrace tailWord_6292842 prefixEnd_6292842 1077084209600191153478251 := by
  unfold tailWord_6292842
  simp only [CollatzResearch.WordTrace]
  refine ⟨57379700867028910173734195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153012535645410427129957853 57379700867028910173734195)
  ·
    refine ⟨86069551300543365260601293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57379700867028910173734195 86069551300543365260601293)
    ·
      refine ⟨32276081737703761972725485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86069551300543365260601293 32276081737703761972725485)
      ·
        refine ⟨12103530651638910739772057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32276081737703761972725485 12103530651638910739772057)
        ·
          refine ⟨9077647988729183054829043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12103530651638910739772057 9077647988729183054829043)
          ·
            refine ⟨13616471983093774582243565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9077647988729183054829043 13616471983093774582243565)
            ·
              refine ⟨5106176993660165468341337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13616471983093774582243565 5106176993660165468341337)
              ·
                refine ⟨3829632745245124101256003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106176993660165468341337 3829632745245124101256003)
                ·
                  refine ⟨5744449117867686151884005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829632745245124101256003 5744449117867686151884005)
                  ·
                    refine ⟨1077084209600191153478251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744449117867686151884005 1077084209600191153478251)
                    ·
                      rfl

theorem cell23_6292842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_6292842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292842 prefixEnd_6292842 := by exact prefixLift 6292842
  have htrace : WordTrace (prefixWord ++ tailWord_6292842) baseStart_6292842 baseEnd_6292842 := by
    simpa [prefixWord, tailWord_6292842, baseEnd_6292842] using wordTrace_append hprefix tailTrace_6292842
  have hstable : (prefixWord ++ tailWord_6292842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292842).length < 2 ^ (prefixWord ++ tailWord_6292842).sum := by decide
  have hdescent : baseEnd_6292842 < baseStart_6292842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292868 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_6292868 : Nat := 118140960795 + 6292868 * 2 ^ 59
def prefixEnd_6292868 : Nat := 4983230072969 + 3 ^ 40 * 6292868 * 2
def baseEnd_6292868 : Nat := 1077088659765863452903211

theorem tailTrace_6292868 : CollatzResearch.WordTrace tailWord_6292868 prefixEnd_6292868 1077088659765863452903211 := by
  unfold tailWord_6292868
  simp only [CollatzResearch.WordTrace]
  refine ⟨114759875883010723567691629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153013167844014298090255505 114759875883010723567691629)
  ·
    refine ⟨43034953456129021337884361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114759875883010723567691629 43034953456129021337884361)
    ·
      refine ⟨32276215092096766003413271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43034953456129021337884361 32276215092096766003413271)
      ·
        refine ⟨48414322638145149005119907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32276215092096766003413271 48414322638145149005119907)
        ·
          refine ⟨72621483957217723507679861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48414322638145149005119907 72621483957217723507679861)
          ·
            refine ⟨6808264120989161578844987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72621483957217723507679861 6808264120989161578844987)
            ·
              refine ⟨10212396181483742368267481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808264120989161578844987 10212396181483742368267481)
              ·
                refine ⟨7659297136112806776200611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212396181483742368267481 7659297136112806776200611)
                ·
                  refine ⟨11488945704169210164300917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659297136112806776200611 11488945704169210164300917)
                  ·
                    refine ⟨1077088659765863452903211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11488945704169210164300917 1077088659765863452903211)
                    ·
                      rfl

theorem cell23_6292868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_6292868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292868 prefixEnd_6292868 := by exact prefixLift 6292868
  have htrace : WordTrace (prefixWord ++ tailWord_6292868) baseStart_6292868 baseEnd_6292868 := by
    simpa [prefixWord, tailWord_6292868, baseEnd_6292868] using wordTrace_append hprefix tailTrace_6292868
  have hstable : (prefixWord ++ tailWord_6292868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292868).length < 2 ^ (prefixWord ++ tailWord_6292868).sum := by decide
  have hdescent : baseEnd_6292868 < baseStart_6292868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292871 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_6292871 : Nat := 118140960795 + 6292871 * 2 ^ 59
def prefixEnd_6292871 : Nat := 4983230072969 + 3 ^ 40 * 6292871 * 2
def baseEnd_6292871 : Nat := 3231267519739553846972119

theorem tailTrace_6292871 : CollatzResearch.WordTrace tailWord_6292871 prefixEnd_6292871 3231267519739553846972119 := by
  unfold tailWord_6292871
  simp only [CollatzResearch.WordTrace]
  refine ⟨229519861185010578647742467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153013240790007052431828311 229519861185010578647742467)
  ·
    refine ⟨344279791777515867971613701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229519861185010578647742467 344279791777515867971613701)
    ·
      refine ⟨64552460958284225244677569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344279791777515867971613701 64552460958284225244677569)
      ·
        refine ⟨48414345718713168933508177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64552460958284225244677569 48414345718713168933508177)
        ·
          refine ⟨36310759289034876700131133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48414345718713168933508177 36310759289034876700131133)
          ·
            refine ⟨13616534733388078762549175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36310759289034876700131133 13616534733388078762549175)
            ·
              refine ⟨20424802100082118143823763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13616534733388078762549175 20424802100082118143823763)
              ·
                refine ⟨30637203150123177215735645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20424802100082118143823763 30637203150123177215735645)
                ·
                  refine ⟨11488951181296191455900867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30637203150123177215735645 11488951181296191455900867)
                  ·
                    refine ⟨17233426771944287183851301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11488951181296191455900867 17233426771944287183851301)
                    ·
                      refine ⟨3231267519739553846972119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17233426771944287183851301 3231267519739553846972119)
                      ·
                        rfl

theorem cell23_6292871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_6292871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292871 prefixEnd_6292871 := by exact prefixLift 6292871
  have htrace : WordTrace (prefixWord ++ tailWord_6292871) baseStart_6292871 baseEnd_6292871 := by
    simpa [prefixWord, tailWord_6292871, baseEnd_6292871] using wordTrace_append hprefix tailTrace_6292871
  have hstable : (prefixWord ++ tailWord_6292871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292871).length < 2 ^ (prefixWord ++ tailWord_6292871).sum := by decide
  have hdescent : baseEnd_6292871 < baseStart_6292871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292898 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6292898 : Nat := 118140960795 + 6292898 * 2 ^ 59
def prefixEnd_6292898 : Nat := 4983230072969 + 3 ^ 40 * 6292898 * 2
def baseEnd_6292898 : Nat := 1077093794572408413778165

theorem tailTrace_6292898 : CollatzResearch.WordTrace tailWord_6292898 prefixEnd_6292898 1077093794572408413778165 := by
  unfold tailWord_6292898
  simp only [CollatzResearch.WordTrace]
  refine ⟨57380211488978190564743837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153013897303941841505983565 57380211488978190564743837)
  ·
    refine ⟨21517579308366821461778939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57380211488978190564743837 21517579308366821461778939)
    ·
      refine ⟨32276368962550232192668409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21517579308366821461778939 32276368962550232192668409)
      ·
        refine ⟨24207276721912674144501307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32276368962550232192668409 24207276721912674144501307)
        ·
          refine ⟨36310915082869011216751961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24207276721912674144501307 36310915082869011216751961)
          ·
            refine ⟨27233186312151758412563971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36310915082869011216751961 27233186312151758412563971)
            ·
              refine ⟨40849779468227637618845957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27233186312151758412563971 40849779468227637618845957)
              ·
                refine ⟨7659333650292682053533617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40849779468227637618845957 7659333650292682053533617)
                ·
                  refine ⟨5744500237719511540150213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7659333650292682053533617 5744500237719511540150213)
                  ·
                    refine ⟨1077093794572408413778165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744500237719511540150213 1077093794572408413778165)
                    ·
                      rfl

theorem cell23_6292898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6292898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292898 prefixEnd_6292898 := by exact prefixLift 6292898
  have htrace : WordTrace (prefixWord ++ tailWord_6292898) baseStart_6292898 baseEnd_6292898 := by
    simpa [prefixWord, tailWord_6292898, baseEnd_6292898] using wordTrace_append hprefix tailTrace_6292898
  have hstable : (prefixWord ++ tailWord_6292898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292898).length < 2 ^ (prefixWord ++ tailWord_6292898).sum := by decide
  have hdescent : baseEnd_6292898 < baseStart_6292898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292944 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_6292944 : Nat := 118140960795 + 6292944 * 2 ^ 59
def prefixEnd_6292944 : Nat := 4983230072969 + 3 ^ 40 * 6292944 * 2
def baseEnd_6292944 : Nat := 3231305003827332061359283

theorem tailTrace_6292944 : CollatzResearch.WordTrace tailWord_6292944 prefixEnd_6292944 3231305003827332061359283 := by
  unfold tailWord_6292944
  simp only [CollatzResearch.WordTrace]
  refine ⟨114761261856873056057574943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153015015809164074743433257 114761261856873056057574943)
  ·
    refine ⟨172141892785309584086362415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114761261856873056057574943 172141892785309584086362415)
    ·
      refine ⟨258212839177964376129543623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172141892785309584086362415 258212839177964376129543623)
      ·
        refine ⟨387319258766946564194315435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258212839177964376129543623 387319258766946564194315435)
        ·
          refine ⟨580978888150419846291473153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387319258766946564194315435 580978888150419846291473153)
          ·
            refine ⟨435734166112814884718604865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580978888150419846291473153 435734166112814884718604865)
            ·
              refine ⟨326800624584611163538953649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435734166112814884718604865 326800624584611163538953649)
              ·
                refine ⟨245100468438458372654215237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326800624584611163538953649 245100468438458372654215237)
                ·
                  refine ⟨45956337832210944872665357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245100468438458372654215237 45956337832210944872665357)
                  ·
                    refine ⟨17233626687079104327249509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45956337832210944872665357 17233626687079104327249509)
                    ·
                      refine ⟨3231305003827332061359283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17233626687079104327249509 3231305003827332061359283)
                      ·
                        rfl

theorem cell23_6292944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_6292944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292944 prefixEnd_6292944 := by exact prefixLift 6292944
  have htrace : WordTrace (prefixWord ++ tailWord_6292944) baseStart_6292944 baseEnd_6292944 := by
    simpa [prefixWord, tailWord_6292944, baseEnd_6292944] using wordTrace_append hprefix tailTrace_6292944
  have hstable : (prefixWord ++ tailWord_6292944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292944).length < 2 ^ (prefixWord ++ tailWord_6292944).sum := by decide
  have hdescent : baseEnd_6292944 < baseStart_6292944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6292982 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_6292982 : Nat := 118140960795 + 6292982 * 2 ^ 59
def prefixEnd_6292982 : Nat := 4983230072969 + 3 ^ 40 * 6292982 * 2
def baseEnd_6292982 : Nat := 3231324516092202912684109

theorem tailTrace_6292982 : CollatzResearch.WordTrace tailWord_6292982 prefixEnd_6292982 3231324516092202912684109 := by
  unfold tailWord_6292982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345244355475527787814575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153015939791738963070022133 14345244355475527787814575)
  ·
    refine ⟨21517866533213291681721863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14345244355475527787814575 21517866533213291681721863)
    ·
      refine ⟨32276799799819937522582795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21517866533213291681721863 32276799799819937522582795)
      ·
        refine ⟨48415199699729906283874193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32276799799819937522582795 48415199699729906283874193)
        ·
          refine ⟨36311399774797429712905645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48415199699729906283874193 36311399774797429712905645)
          ·
            refine ⟨13616774915549036142339617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36311399774797429712905645 13616774915549036142339617)
            ·
              refine ⟨10212581186661777106754713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13616774915549036142339617 10212581186661777106754713)
              ·
                refine ⟨7659435889996332830066035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212581186661777106754713 7659435889996332830066035)
                ·
                  refine ⟨11489153834994499245099053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659435889996332830066035 11489153834994499245099053)
                  ·
                    refine ⟨4308432688122937216912145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11489153834994499245099053 4308432688122937216912145)
                    ·
                      refine ⟨3231324516092202912684109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308432688122937216912145 3231324516092202912684109)
                      ·
                        rfl

theorem cell23_6292982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_6292982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6292982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6292982 prefixEnd_6292982 := by exact prefixLift 6292982
  have htrace : WordTrace (prefixWord ++ tailWord_6292982) baseStart_6292982 baseEnd_6292982 := by
    simpa [prefixWord, tailWord_6292982, baseEnd_6292982] using wordTrace_append hprefix tailTrace_6292982
  have hstable : (prefixWord ++ tailWord_6292982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6292982).length < 2 ^ (prefixWord ++ tailWord_6292982).sum := by decide
  have hdescent : baseEnd_6292982 < baseStart_6292982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6292982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293048 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_6293048 : Nat := 118140960795 + 6293048 * 2 ^ 59
def prefixEnd_6293048 : Nat := 4983230072969 + 3 ^ 40 * 6293048 * 2
def baseEnd_6293048 : Nat := 1077119468605133218152935

theorem tailTrace_6293048 : CollatzResearch.WordTrace tailWord_6293048 prefixEnd_6293048 1077119468605133218152935 := by
  unfold tailWord_6293048
  simp only [CollatzResearch.WordTrace]
  refine ⟨114763158452684668938467899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153017544603579558584623865 114763158452684668938467899)
  ·
    refine ⟨172144737679027003407701849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114763158452684668938467899 172144737679027003407701849)
    ·
      refine ⟨129108553259270252555776387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172144737679027003407701849 129108553259270252555776387)
      ·
        refine ⟨193662829888905378833664581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129108553259270252555776387 193662829888905378833664581)
        ·
          refine ⟨36311780604169758531312109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193662829888905378833664581 36311780604169758531312109)
          ·
            refine ⟨13616917726563659449242041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36311780604169758531312109 13616917726563659449242041)
            ·
              refine ⟨10212688294922744586931531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13616917726563659449242041 10212688294922744586931531)
              ·
                refine ⟨15319032442384116880397297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10212688294922744586931531 15319032442384116880397297)
                ·
                  refine ⟨11489274331788087660297973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15319032442384116880397297 11489274331788087660297973)
                  ·
                    refine ⟨1077119468605133218152935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11489274331788087660297973 1077119468605133218152935)
                    ·
                      rfl

theorem cell23_6293048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_6293048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293048 prefixEnd_6293048 := by exact prefixLift 6293048
  have htrace : WordTrace (prefixWord ++ tailWord_6293048) baseStart_6293048 baseEnd_6293048 := by
    simpa [prefixWord, tailWord_6293048, baseEnd_6293048] using wordTrace_append hprefix tailTrace_6293048
  have hstable : (prefixWord ++ tailWord_6293048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293048).length < 2 ^ (prefixWord ++ tailWord_6293048).sum := by decide
  have hdescent : baseEnd_6293048 < baseStart_6293048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293068 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6293068 : Nat := 118140960795 + 6293068 * 2 ^ 59
def prefixEnd_6293068 : Nat := 4983230072969 + 3 ^ 40 * 6293068 * 2
def baseEnd_6293068 : Nat := 3231368675428489576208713

theorem tailTrace_6293068 : CollatzResearch.WordTrace tailWord_6293068 prefixEnd_6293068 3231368675428489576208713 := by
  unfold tailWord_6293068
  simp only [CollatzResearch.WordTrace]
  refine ⟨114763523182648440646331929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153018030910197920861775905 114763523182648440646331929)
  ·
    refine ⟨86072642386986330484748947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114763523182648440646331929 86072642386986330484748947)
    ·
      refine ⟨129108963580479495727123421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86072642386986330484748947 129108963580479495727123421)
      ·
        refine ⟨48415861342679810897671283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129108963580479495727123421 48415861342679810897671283)
        ·
          refine ⟨72623792014019716346506925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48415861342679810897671283 72623792014019716346506925)
          ·
            refine ⟨27233922005257393629940097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72623792014019716346506925 27233922005257393629940097)
            ·
              refine ⟨20425441503943045222455073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27233922005257393629940097 20425441503943045222455073)
              ·
                refine ⟨15319081127957283916841305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20425441503943045222455073 15319081127957283916841305)
                ·
                  refine ⟨11489310845967962937630979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15319081127957283916841305 11489310845967962937630979)
                  ·
                    refine ⟨17233966268951944406446469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11489310845967962937630979 17233966268951944406446469)
                    ·
                      refine ⟨3231368675428489576208713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17233966268951944406446469 3231368675428489576208713)
                      ·
                        rfl

theorem cell23_6293068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6293068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293068 prefixEnd_6293068 := by exact prefixLift 6293068
  have htrace : WordTrace (prefixWord ++ tailWord_6293068) baseStart_6293068 baseEnd_6293068 := by
    simpa [prefixWord, tailWord_6293068, baseEnd_6293068] using wordTrace_append hprefix tailTrace_6293068
  have hstable : (prefixWord ++ tailWord_6293068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293068).length < 2 ^ (prefixWord ++ tailWord_6293068).sum := by decide
  have hdescent : baseEnd_6293068 < baseStart_6293068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293069 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 5]
def baseStart_6293069 : Nat := 118140960795 + 6293069 * 2 ^ 59
def prefixEnd_6293069 : Nat := 4983230072969 + 3 ^ 40 * 6293069 * 2
def baseEnd_6293069 : Nat := 359041020989904896921801

theorem tailTrace_6293069 : CollatzResearch.WordTrace tailWord_6293069 prefixEnd_6293069 359041020989904896921801 := by
  unfold tailWord_6293069
  simp only [CollatzResearch.WordTrace]
  refine ⟨229527082838293258463450261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153018055225528838975633507 229527082838293258463450261)
  ·
    refine ⟨10759082008044996490474231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229527082838293258463450261 10759082008044996490474231)
    ·
      refine ⟨16138623012067494735711347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759082008044996490474231 16138623012067494735711347)
      ·
        refine ⟨24207934518101242103567021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16138623012067494735711347 24207934518101242103567021)
        ·
          refine ⟨9077975444287965788837633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24207934518101242103567021 9077975444287965788837633)
          ·
            refine ⟨6808481583215974341628225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9077975444287965788837633 6808481583215974341628225)
            ·
              refine ⟨5106361187411980756221169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6808481583215974341628225 5106361187411980756221169)
              ·
                refine ⟨3829770890558985567165877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106361187411980756221169 3829770890558985567165877)
                ·
                  refine ⟨359041020989904896921801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3829770890558985567165877 359041020989904896921801)
                  ·
                    rfl

theorem cell23_6293069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_6293069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293069 prefixEnd_6293069 := by exact prefixLift 6293069
  have htrace : WordTrace (prefixWord ++ tailWord_6293069) baseStart_6293069 baseEnd_6293069 := by
    simpa [prefixWord, tailWord_6293069, baseEnd_6293069] using wordTrace_append hprefix tailTrace_6293069
  have hstable : (prefixWord ++ tailWord_6293069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293069).length < 2 ^ (prefixWord ++ tailWord_6293069).sum := by decide
  have hdescent : baseEnd_6293069 < baseStart_6293069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293071 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_6293071 : Nat := 118140960795 + 6293071 * 2 ^ 59
def prefixEnd_6293071 : Nat := 4983230072969 + 3 ^ 40 * 6293071 * 2
def baseEnd_6293071 : Nat := 3231370215870453064471199

theorem tailTrace_6293071 : CollatzResearch.WordTrace tailWord_6293071 prefixEnd_6293071 3231370215870453064471199 := by
  unfold tailWord_6293071
  simp only [CollatzResearch.WordTrace]
  refine ⟨229527155784286012805023067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153018103856190675203348711 229527155784286012805023067)
  ·
    refine ⟨344290733676429019207534601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229527155784286012805023067 344290733676429019207534601)
    ·
      refine ⟨258218050257321764405650951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344290733676429019207534601 258218050257321764405650951)
      ·
        refine ⟨387327075385982646608476427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258218050257321764405650951 387327075385982646608476427)
        ·
          refine ⟨580990613078973969912714641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387327075385982646608476427 580990613078973969912714641)
          ·
            refine ⟨435742959809230477434535981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580990613078973969912714641 435742959809230477434535981)
            ·
              refine ⟨163403609928461429037950993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435742959809230477434535981 163403609928461429037950993)
              ·
                refine ⟨122552707446346071778463245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163403609928461429037950993 122552707446346071778463245)
                ·
                  refine ⟨45957265292379776916923717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122552707446346071778463245 45957265292379776916923717)
                  ·
                    refine ⟨8616987242321208171923197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45957265292379776916923717 8616987242321208171923197)
                    ·
                      refine ⟨3231370215870453064471199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8616987242321208171923197 3231370215870453064471199)
                      ·
                        rfl

theorem cell23_6293071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_6293071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293071 prefixEnd_6293071 := by exact prefixLift 6293071
  have htrace : WordTrace (prefixWord ++ tailWord_6293071) baseStart_6293071 baseEnd_6293071 := by
    simpa [prefixWord, tailWord_6293071, baseEnd_6293071] using wordTrace_append hprefix tailTrace_6293071
  have hstable : (prefixWord ++ tailWord_6293071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293071).length < 2 ^ (prefixWord ++ tailWord_6293071).sum := by decide
  have hdescent : baseEnd_6293071 < baseStart_6293071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293102 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_6293102 : Nat := 118140960795 + 6293102 * 2 ^ 59
def prefixEnd_6293102 : Nat := 4983230072969 + 3 ^ 40 * 6293102 * 2
def baseEnd_6293102 : Nat := 3231386133770742443183557

theorem tailTrace_6293102 : CollatzResearch.WordTrace tailWord_6293102 prefixEnd_6293102 3231386133770742443183557 := by
  unfold tailWord_6293102
  simp only [CollatzResearch.WordTrace]
  refine ⟨28691035805896713137425195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153018857631449136732934373 28691035805896713137425195)
  ·
    refine ⟨43036553708845069706137793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28691035805896713137425195 43036553708845069706137793)
    ·
      refine ⟨32277415281633802279603345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43036553708845069706137793 32277415281633802279603345)
      ·
        refine ⟨24208061461225351709702509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32277415281633802279603345 24208061461225351709702509)
        ·
          refine ⟨9078023047959506891138441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24208061461225351709702509 9078023047959506891138441)
          ·
            refine ⟨6808517285969630168353831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078023047959506891138441 6808517285969630168353831)
            ·
              refine ⟨10212775928954445252530747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808517285969630168353831 10212775928954445252530747)
              ·
                refine ⟨15319163893431667878796121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10212775928954445252530747 15319163893431667878796121)
                ·
                  refine ⟨11489372920073750909097091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15319163893431667878796121 11489372920073750909097091)
                  ·
                    refine ⟨17234059380110626363645637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11489372920073750909097091 17234059380110626363645637)
                    ·
                      refine ⟨3231386133770742443183557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17234059380110626363645637 3231386133770742443183557)
                      ·
                        rfl

theorem cell23_6293102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_6293102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293102 prefixEnd_6293102 := by exact prefixLift 6293102
  have htrace : WordTrace (prefixWord ++ tailWord_6293102) baseStart_6293102 baseEnd_6293102 := by
    simpa [prefixWord, tailWord_6293102, baseEnd_6293102] using wordTrace_append hprefix tailTrace_6293102
  have hstable : (prefixWord ++ tailWord_6293102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293102).length < 2 ^ (prefixWord ++ tailWord_6293102).sum := by decide
  have hdescent : baseEnd_6293102 < baseStart_6293102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293168 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_6293168 : Nat := 118140960795 + 6293168 * 2 ^ 59
def prefixEnd_6293168 : Nat := 4983230072969 + 3 ^ 40 * 6293168 * 2
def baseEnd_6293168 : Nat := 1077140007831313061652751

theorem tailTrace_6293168 : CollatzResearch.WordTrace tailWord_6293168 prefixEnd_6293168 1077140007831313061652751 := by
  unfold tailWord_6293168
  simp only [CollatzResearch.WordTrace]
  refine ⟨114765346832467299185652079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153020462443289732247536105 114765346832467299185652079)
  ·
    refine ⟨172148020248700948778478119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114765346832467299185652079 172148020248700948778478119)
    ·
      refine ⟨258222030373051423167717179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172148020248700948778478119 258222030373051423167717179)
      ·
        refine ⟨387333045559577134751575769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258222030373051423167717179 387333045559577134751575769)
        ·
          refine ⟨290499784169682851063681827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387333045559577134751575769 290499784169682851063681827)
          ·
            refine ⟨435749676254524276595522741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290499784169682851063681827 435749676254524276595522741)
            ·
              refine ⟨40851532148861650930830257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435749676254524276595522741 40851532148861650930830257)
              ·
                refine ⟨30638649111646238198122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40851532148861650930830257 30638649111646238198122693)
                ·
                  refine ⟨5744746708433669662148005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30638649111646238198122693 5744746708433669662148005)
                  ·
                    refine ⟨1077140007831313061652751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744746708433669662148005 1077140007831313061652751)
                    ·
                      rfl

theorem cell23_6293168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_6293168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293168 prefixEnd_6293168 := by exact prefixLift 6293168
  have htrace : WordTrace (prefixWord ++ tailWord_6293168) baseStart_6293168 baseEnd_6293168 := by
    simpa [prefixWord, tailWord_6293168, baseEnd_6293168] using wordTrace_append hprefix tailTrace_6293168
  have hstable : (prefixWord ++ tailWord_6293168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293168).length < 2 ^ (prefixWord ++ tailWord_6293168).sum := by decide
  have hdescent : baseEnd_6293168 < baseStart_6293168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293175 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_6293175 : Nat := 118140960795 + 6293175 * 2 ^ 59
def prefixEnd_6293175 : Nat := 4983230072969 + 3 ^ 40 * 6293175 * 2
def baseEnd_6293175 : Nat := 3231423617858520657570721

theorem tailTrace_6293175 : CollatzResearch.WordTrace tailWord_6293175 prefixEnd_6293175 3231423617858520657570721 := by
  unfold tailWord_6293175
  simp only [CollatzResearch.WordTrace]
  refine ⟨229530948975909238566808979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153020632650606159044539319 229530948975909238566808979)
  ·
    refine ⟨344296423463863857850213469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229530948975909238566808979 344296423463863857850213469)
    ·
      refine ⟨129111158798948946693830051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344296423463863857850213469 129111158798948946693830051)
      ·
        refine ⟨193666738198423420040745077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129111158798948946693830051 193666738198423420040745077)
        ·
          refine ⟨18156256706102195628819851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193666738198423420040745077 18156256706102195628819851)
          ·
            refine ⟨27234385059153293443229777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18156256706102195628819851 27234385059153293443229777)
            ·
              refine ⟨20425788794364970082422333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27234385059153293443229777 20425788794364970082422333)
              ·
                refine ⟨7659670797886863780908375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20425788794364970082422333 7659670797886863780908375)
                ·
                  refine ⟨11489506196830295671362563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659670797886863780908375 11489506196830295671362563)
                  ·
                    refine ⟨17234259295245443507043845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11489506196830295671362563 17234259295245443507043845)
                    ·
                      refine ⟨3231423617858520657570721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17234259295245443507043845 3231423617858520657570721)
                      ·
                        rfl

theorem cell23_6293175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_6293175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293175 prefixEnd_6293175 := by exact prefixLift 6293175
  have htrace : WordTrace (prefixWord ++ tailWord_6293175) baseStart_6293175 baseEnd_6293175 := by
    simpa [prefixWord, tailWord_6293175, baseEnd_6293175] using wordTrace_append hprefix tailTrace_6293175
  have hstable : (prefixWord ++ tailWord_6293175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293175).length < 2 ^ (prefixWord ++ tailWord_6293175).sum := by decide
  have hdescent : baseEnd_6293175 < baseStart_6293175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293178 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_6293178 : Nat := 118140960795 + 6293178 * 2 ^ 59
def prefixEnd_6293178 : Nat := 4983230072969 + 3 ^ 40 * 6293178 * 2
def baseEnd_6293178 : Nat := 3231425158300484145833207

theorem tailTrace_6293178 : CollatzResearch.WordTrace tailWord_6293178 prefixEnd_6293178 3231425158300484145833207 := by
  unfold tailWord_6293178
  simp only [CollatzResearch.WordTrace]
  refine ⟨57382764598724592519792047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153020705596598913386112125 57382764598724592519792047)
  ·
    refine ⟨86074146898086888779688071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57382764598724592519792047 86074146898086888779688071)
    ·
      refine ⟨129111220347130333169532107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86074146898086888779688071 129111220347130333169532107)
      ·
        refine ⟨193666830520695499754298161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129111220347130333169532107 193666830520695499754298161)
        ·
          refine ⟨145250122890521624815723621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193666830520695499754298161 145250122890521624815723621)
          ·
            refine ⟨27234398041972804652948179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145250122890521624815723621 27234398041972804652948179)
            ·
              refine ⟨40851597062959206979422269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27234398041972804652948179 40851597062959206979422269)
              ·
                refine ⟨15319348898609702617283351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40851597062959206979422269 15319348898609702617283351)
                ·
                  refine ⟨22979023347914553925925027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15319348898609702617283351 22979023347914553925925027)
                  ·
                    refine ⟨34468535021871830888887541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22979023347914553925925027 34468535021871830888887541)
                    ·
                      refine ⟨3231425158300484145833207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34468535021871830888887541 3231425158300484145833207)
                      ·
                        rfl

theorem cell23_6293178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_6293178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293178 prefixEnd_6293178 := by exact prefixLift 6293178
  have htrace : WordTrace (prefixWord ++ tailWord_6293178) baseStart_6293178 baseEnd_6293178 := by
    simpa [prefixWord, tailWord_6293178, baseEnd_6293178] using wordTrace_append hprefix tailTrace_6293178
  have hstable : (prefixWord ++ tailWord_6293178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293178).length < 2 ^ (prefixWord ++ tailWord_6293178).sum := by decide
  have hdescent : baseEnd_6293178 < baseStart_6293178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293188 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6293188 : Nat := 118140960795 + 6293188 * 2 ^ 59
def prefixEnd_6293188 : Nat := 4983230072969 + 3 ^ 40 * 6293188 * 2
def baseEnd_6293188 : Nat := 3231430293107029106708161

theorem tailTrace_6293188 : CollatzResearch.WordTrace tailWord_6293188 prefixEnd_6293188 3231430293107029106708161 := by
  unfold tailWord_6293188
  simp only [CollatzResearch.WordTrace]
  refine ⟨114765711562431070893516109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153020948749908094524688145 114765711562431070893516109)
  ·
    refine ⟨43037141835911651585068541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114765711562431070893516109 43037141835911651585068541)
    ·
      refine ⟨16138928188466869344400703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43037141835911651585068541 16138928188466869344400703)
      ·
        refine ⟨24208392282700304016601055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16138928188466869344400703 24208392282700304016601055)
        ·
          refine ⟨36312588424050456024901583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24208392282700304016601055 36312588424050456024901583)
          ·
            refine ⟨54468882636075684037352375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36312588424050456024901583 54468882636075684037352375)
            ·
              refine ⟨81703323954113526056028563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54468882636075684037352375 81703323954113526056028563)
              ·
                refine ⟨122554985931170289084042845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81703323954113526056028563 122554985931170289084042845)
                ·
                  refine ⟨45958119724188858406516067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122554985931170289084042845 45958119724188858406516067)
                  ·
                    refine ⟨68937179586283287609774101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45958119724188858406516067 68937179586283287609774101)
                    ·
                      refine ⟨3231430293107029106708161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68937179586283287609774101 3231430293107029106708161)
                      ·
                        rfl

theorem cell23_6293188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6293188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293188 prefixEnd_6293188 := by exact prefixLift 6293188
  have htrace : WordTrace (prefixWord ++ tailWord_6293188) baseStart_6293188 baseEnd_6293188 := by
    simpa [prefixWord, tailWord_6293188, baseEnd_6293188] using wordTrace_append hprefix tailTrace_6293188
  have hstable : (prefixWord ++ tailWord_6293188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293188).length < 2 ^ (prefixWord ++ tailWord_6293188).sum := by decide
  have hdescent : baseEnd_6293188 < baseStart_6293188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293198 : List Nat := [4, 1, 1, 1, 3, 1, 4, 8]
def baseStart_6293198 : Nat := 118140960795 + 6293198 * 2 ^ 59
def prefixEnd_6293198 : Nat := 4983230072969 + 3 ^ 40 * 6293198 * 2
def baseEnd_6293198 : Nat := 119682793626428669169745

theorem tailTrace_6293198 : CollatzResearch.WordTrace tailWord_6293198 prefixEnd_6293198 119682793626428669169745 := by
  unfold tailWord_6293198
  simp only [CollatzResearch.WordTrace]
  refine ⟨28691473481853239186862031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153021191903217275663264165 28691473481853239186862031)
  ·
    refine ⟨43037210222779858780293047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28691473481853239186862031 43037210222779858780293047)
    ·
      refine ⟨64555815334169788170439571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43037210222779858780293047 64555815334169788170439571)
      ·
        refine ⟨96833723001254682255659357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64555815334169788170439571 96833723001254682255659357)
        ·
          refine ⟨36312646125470505845872259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96833723001254682255659357 36312646125470505845872259)
          ·
            refine ⟨54468969188205758768808389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36312646125470505845872259 54468969188205758768808389)
            ·
              refine ⟨10212931722788579769151573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54468969188205758768808389 10212931722788579769151573)
              ·
                refine ⟨119682793626428669169745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10212931722788579769151573 119682793626428669169745)
                ·
                  rfl

theorem cell23_6293198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_6293198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293198 prefixEnd_6293198 := by exact prefixLift 6293198
  have htrace : WordTrace (prefixWord ++ tailWord_6293198) baseStart_6293198 baseEnd_6293198 := by
    simpa [prefixWord, tailWord_6293198, baseEnd_6293198] using wordTrace_append hprefix tailTrace_6293198
  have hstable : (prefixWord ++ tailWord_6293198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293198).length < 2 ^ (prefixWord ++ tailWord_6293198).sum := by decide
  have hdescent : baseEnd_6293198 < baseStart_6293198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293202 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_6293202 : Nat := 118140960795 + 6293202 * 2 ^ 59
def prefixEnd_6293202 : Nat := 4983230072969 + 3 ^ 40 * 6293202 * 2
def baseEnd_6293202 : Nat := 1077145827278730683977699

theorem tailTrace_6293202 : CollatzResearch.WordTrace tailWord_6293202 prefixEnd_6293202 1077145827278730683977699 := by
  unfold tailWord_6293202
  simp only [CollatzResearch.WordTrace]
  refine ⟨57382983436702855544510465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153021289164540948118694573 57382983436702855544510465)
  ·
    refine ⟨43037237577527141658382849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57382983436702855544510465 43037237577527141658382849)
    ·
      refine ⟨32277928183145356243787137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43037237577527141658382849 32277928183145356243787137)
      ·
        refine ⟨24208446137359017182840353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32277928183145356243787137 24208446137359017182840353)
        ·
          refine ⟨18156334603019262887130265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24208446137359017182840353 18156334603019262887130265)
          ·
            refine ⟨13617250952264447165347699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18156334603019262887130265 13617250952264447165347699)
            ·
              refine ⟨20425876428396670748021549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13617250952264447165347699 20425876428396670748021549)
              ·
                refine ⟨7659703660648751530508081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20425876428396670748021549 7659703660648751530508081)
                ·
                  refine ⟨5744777745486563647881061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7659703660648751530508081 5744777745486563647881061)
                  ·
                    refine ⟨1077145827278730683977699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744777745486563647881061 1077145827278730683977699)
                    ·
                      rfl

theorem cell23_6293202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_6293202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293202 prefixEnd_6293202 := by exact prefixLift 6293202
  have htrace : WordTrace (prefixWord ++ tailWord_6293202) baseStart_6293202 baseEnd_6293202 := by
    simpa [prefixWord, tailWord_6293202, baseEnd_6293202] using wordTrace_append hprefix tailTrace_6293202
  have hstable : (prefixWord ++ tailWord_6293202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293202).length < 2 ^ (prefixWord ++ tailWord_6293202).sum := by decide
  have hdescent : baseEnd_6293202 < baseStart_6293202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293206 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6293206 : Nat := 118140960795 + 6293206 * 2 ^ 59
def prefixEnd_6293206 : Nat := 4983230072969 + 3 ^ 40 * 6293206 * 2
def baseEnd_6293206 : Nat := 1077146511919603345427693

theorem tailTrace_6293206 : CollatzResearch.WordTrace tailWord_6293206 prefixEnd_6293206 1077146511919603345427693 := by
  unfold tailWord_6293206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345754977424808178824217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153021386425864620574124981 14345754977424808178824217)
  ·
    refine ⟨10759316233068606134118163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14345754977424808178824217 10759316233068606134118163)
    ·
      refine ⟨16138974349602909201177245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759316233068606134118163 16138974349602909201177245)
      ·
        refine ⟨6052115381101090950441467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16138974349602909201177245 6052115381101090950441467)
        ·
          refine ⟨9078173071651636425662201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6052115381101090950441467 9078173071651636425662201)
          ·
            refine ⟨6808629803738727319246651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078173071651636425662201 6808629803738727319246651)
            ·
              refine ⟨10212944705608090978869977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808629803738727319246651 10212944705608090978869977)
              ·
                refine ⟨7659708529206068234152483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212944705608090978869977 7659708529206068234152483)
                ·
                  refine ⟨11489562793809102351228725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659708529206068234152483 11489562793809102351228725)
                  ·
                    refine ⟨1077146511919603345427693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11489562793809102351228725 1077146511919603345427693)
                    ·
                      rfl

theorem cell23_6293206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6293206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293206 prefixEnd_6293206 := by exact prefixLift 6293206
  have htrace : WordTrace (prefixWord ++ tailWord_6293206) baseStart_6293206 baseEnd_6293206 := by
    simpa [prefixWord, tailWord_6293206, baseEnd_6293206] using wordTrace_append hprefix tailTrace_6293206
  have hstable : (prefixWord ++ tailWord_6293206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293206).length < 2 ^ (prefixWord ++ tailWord_6293206).sum := by decide
  have hdescent : baseEnd_6293206 < baseStart_6293206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293229 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_6293229 : Nat := 118140960795 + 6293229 * 2 ^ 59
def prefixEnd_6293229 : Nat := 4983230072969 + 3 ^ 40 * 6293229 * 2
def baseEnd_6293229 : Nat := 3231451345813863446295473

theorem tailTrace_6293229 : CollatzResearch.WordTrace tailWord_6293229 prefixEnd_6293229 3231451345813863446295473 := by
  unfold tailWord_6293229
  simp only [CollatzResearch.WordTrace]
  refine ⟨229532918517713605789274741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153021945678475737192849827 229532918517713605789274741)
  ·
    refine ⟨21518711111035650542744507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229532918517713605789274741 21518711111035650542744507)
    ·
      refine ⟨32278066666553475814116761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21518711111035650542744507 32278066666553475814116761)
      ·
        refine ⟨24208549999915106860587571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32278066666553475814116761 24208549999915106860587571)
        ·
          refine ⟨36312824999872660290881357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24208549999915106860587571 36312824999872660290881357)
          ·
            refine ⟨13617309374952247609080509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36312824999872660290881357 13617309374952247609080509)
            ·
              refine ⟨5106491015607092853405191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13617309374952247609080509 5106491015607092853405191)
              ·
                refine ⟨7659736523410639280107787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106491015607092853405191 7659736523410639280107787)
                ·
                  refine ⟨11489604785115958920161681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659736523410639280107787 11489604785115958920161681)
                  ·
                    refine ⟨8617203588836969190121261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11489604785115958920161681 8617203588836969190121261)
                    ·
                      refine ⟨3231451345813863446295473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617203588836969190121261 3231451345813863446295473)
                      ·
                        rfl

theorem cell23_6293229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_6293229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293229 prefixEnd_6293229 := by exact prefixLift 6293229
  have htrace : WordTrace (prefixWord ++ tailWord_6293229) baseStart_6293229 baseEnd_6293229 := by
    simpa [prefixWord, tailWord_6293229, baseEnd_6293229] using wordTrace_append hprefix tailTrace_6293229
  have hstable : (prefixWord ++ tailWord_6293229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293229).length < 2 ^ (prefixWord ++ tailWord_6293229).sum := by decide
  have hdescent : baseEnd_6293229 < baseStart_6293229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293236 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6293236 : Nat := 118140960795 + 6293236 * 2 ^ 59
def prefixEnd_6293236 : Nat := 4983230072969 + 3 ^ 40 * 6293236 * 2
def baseEnd_6293236 : Nat := 1077151646726148306302647

theorem tailTrace_6293236 : CollatzResearch.WordTrace tailWord_6293236 prefixEnd_6293236 1077151646726148306302647 := by
  unfold tailWord_6293236
  simp only [CollatzResearch.WordTrace]
  refine ⟨114766586914344122992389781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153022115885792163989853041 114766586914344122992389781)
  ·
    refine ⟨5379683761609880765268271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114766586914344122992389781 5379683761609880765268271)
    ·
      refine ⟨8069525642414821147902407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379683761609880765268271 8069525642414821147902407)
      ·
        refine ⟨12104288463622231721853611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069525642414821147902407 12104288463622231721853611)
        ·
          refine ⟨18156432695433347582780417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12104288463622231721853611 18156432695433347582780417)
          ·
            refine ⟨13617324521575010687085313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18156432695433347582780417 13617324521575010687085313)
            ·
              refine ⟨10212993391181258015313985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13617324521575010687085313 10212993391181258015313985)
              ·
                refine ⟨7659745043385943511485489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212993391181258015313985 7659745043385943511485489)
                ·
                  refine ⟨5744808782539457633614117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7659745043385943511485489 5744808782539457633614117)
                  ·
                    refine ⟨1077151646726148306302647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744808782539457633614117 1077151646726148306302647)
                    ·
                      rfl

theorem cell23_6293236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6293236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293236 prefixEnd_6293236 := by exact prefixLift 6293236
  have htrace : WordTrace (prefixWord ++ tailWord_6293236) baseStart_6293236 baseEnd_6293236 := by
    simpa [prefixWord, tailWord_6293236, baseEnd_6293236] using wordTrace_append hprefix tailTrace_6293236
  have hstable : (prefixWord ++ tailWord_6293236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293236).length < 2 ^ (prefixWord ++ tailWord_6293236).sum := by decide
  have hdescent : baseEnd_6293236 < baseStart_6293236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293252 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_6293252 : Nat := 118140960795 + 6293252 * 2 ^ 59
def prefixEnd_6293252 : Nat := 4983230072969 + 3 ^ 40 * 6293252 * 2
def baseEnd_6293252 : Nat := 3231463155868916856307867

theorem tailTrace_6293252 : CollatzResearch.WordTrace tailWord_6293252 prefixEnd_6293252 3231463155868916856307867 := by
  unfold tailWord_6293252
  simp only [CollatzResearch.WordTrace]
  refine ⟨114766878698315140358681005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153022504931086853811574673 114766878698315140358681005)
  ·
    refine ⟨43037579511868177634505377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114766878698315140358681005 43037579511868177634505377)
    ·
      refine ⟨32278184633901133225879033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43037579511868177634505377 32278184633901133225879033)
      ·
        refine ⟨24208638475425849919409275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32278184633901133225879033 24208638475425849919409275)
        ·
          refine ⟨36312957713138774879113913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24208638475425849919409275 36312957713138774879113913)
          ·
            refine ⟨27234718284854081159335435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36312957713138774879113913 27234718284854081159335435)
            ·
              refine ⟨40852077427281121739003153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27234718284854081159335435 40852077427281121739003153)
              ·
                refine ⟨30639058070460841304252365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40852077427281121739003153 30639058070460841304252365)
                ·
                  refine ⟨11489646776422815489094637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30639058070460841304252365 11489646776422815489094637)
                  ·
                    refine ⟨4308617541158555808410489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11489646776422815489094637 4308617541158555808410489)
                    ·
                      refine ⟨3231463155868916856307867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308617541158555808410489 3231463155868916856307867)
                      ·
                        rfl

theorem cell23_6293252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_6293252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293252 prefixEnd_6293252 := by exact prefixLift 6293252
  have htrace : WordTrace (prefixWord ++ tailWord_6293252) baseStart_6293252 baseEnd_6293252 := by
    simpa [prefixWord, tailWord_6293252, baseEnd_6293252] using wordTrace_append hprefix tailTrace_6293252
  have hstable : (prefixWord ++ tailWord_6293252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293252).length < 2 ^ (prefixWord ++ tailWord_6293252).sum := by decide
  have hdescent : baseEnd_6293252 < baseStart_6293252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293258 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_6293258 : Nat := 118140960795 + 6293258 * 2 ^ 59
def prefixEnd_6293258 : Nat := 4983230072969 + 3 ^ 40 * 6293258 * 2
def baseEnd_6293258 : Nat := 1077155412250947944277613

theorem tailTrace_6293258 : CollatzResearch.WordTrace tailWord_6293258 prefixEnd_6293258 1077155412250947944277613 := by
  unfold tailWord_6293258
  simp only [CollatzResearch.WordTrace]
  refine ⟨57383494058652135935520107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153022650823072362494720285 57383494058652135935520107)
  ·
    refine ⟨86075241087978203903280161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57383494058652135935520107 86075241087978203903280161)
    ·
      refine ⟨64556430815983652927460121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86075241087978203903280161 64556430815983652927460121)
      ·
        refine ⟨48417323111987739695595091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64556430815983652927460121 48417323111987739695595091)
        ·
          refine ⟨72625984667981609543392637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48417323111987739695595091 72625984667981609543392637)
          ·
            refine ⟨27234744250493103578772239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72625984667981609543392637 27234744250493103578772239)
            ·
              refine ⟨40852116375739655368158359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27234744250493103578772239 40852116375739655368158359)
              ·
                refine ⟨61278174563609483052237539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40852116375739655368158359 61278174563609483052237539)
                ·
                  refine ⟨91917261845414224578356309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61278174563609483052237539 91917261845414224578356309)
                  ·
                    refine ⟨1077155412250947944277613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91917261845414224578356309 1077155412250947944277613)
                    ·
                      rfl

theorem cell23_6293258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_6293258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293258 prefixEnd_6293258 := by exact prefixLift 6293258
  have htrace : WordTrace (prefixWord ++ tailWord_6293258) baseStart_6293258 baseEnd_6293258 := by
    simpa [prefixWord, tailWord_6293258, baseEnd_6293258] using wordTrace_append hprefix tailTrace_6293258
  have hstable : (prefixWord ++ tailWord_6293258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293258).length < 2 ^ (prefixWord ++ tailWord_6293258).sum := by decide
  have hdescent : baseEnd_6293258 < baseStart_6293258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293282 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_6293282 : Nat := 118140960795 + 6293282 * 2 ^ 59
def prefixEnd_6293282 : Nat := 4983230072969 + 3 ^ 40 * 6293282 * 2
def baseEnd_6293282 : Nat := 3231478560288551738932729

theorem tailTrace_6293282 : CollatzResearch.WordTrace tailWord_6293282 prefixEnd_6293282 3231478560288551738932729 := by
  unfold tailWord_6293282
  simp only [CollatzResearch.WordTrace]
  refine ⟨57383712896630398960238525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153023234391014397227302733 57383712896630398960238525)
  ·
    refine ⟨21518892336236399610089447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57383712896630398960238525 21518892336236399610089447)
    ·
      refine ⟨32278338504354599415134171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21518892336236399610089447 32278338504354599415134171)
      ·
        refine ⟨48417507756531899122701257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32278338504354599415134171 48417507756531899122701257)
        ·
          refine ⟨36313130817398924342025943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48417507756531899122701257 36313130817398924342025943)
          ·
            refine ⟨54469696226098386513038915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36313130817398924342025943 54469696226098386513038915)
            ·
              refine ⟨81704544339147579769558373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54469696226098386513038915 81704544339147579769558373)
              ·
                refine ⟨15319602063590171206792195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81704544339147579769558373 15319602063590171206792195)
                ·
                  refine ⟨22979403095385256810188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15319602063590171206792195 22979403095385256810188293)
                  ·
                    refine ⟨4308638080384735651910305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22979403095385256810188293 4308638080384735651910305)
                    ·
                      refine ⟨3231478560288551738932729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308638080384735651910305 3231478560288551738932729)
                      ·
                        rfl

theorem cell23_6293282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_6293282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293282 prefixEnd_6293282 := by exact prefixLift 6293282
  have htrace : WordTrace (prefixWord ++ tailWord_6293282) baseStart_6293282 baseEnd_6293282 := by
    simpa [prefixWord, tailWord_6293282, baseEnd_6293282] using wordTrace_append hprefix tailTrace_6293282
  have hstable : (prefixWord ++ tailWord_6293282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293282).length < 2 ^ (prefixWord ++ tailWord_6293282).sum := by decide
  have hdescent : baseEnd_6293282 < baseStart_6293282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293299 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 4, 2, 2]
def baseStart_6293299 : Nat := 118140960795 + 6293299 * 2 ^ 59
def prefixEnd_6293299 : Nat := 4983230072969 + 3 ^ 40 * 6293299 * 2
def baseEnd_6293299 : Nat := 3231487289459678172420151

theorem tailTrace_6293299 : CollatzResearch.WordTrace tailWord_6293299 prefixEnd_6293299 3231487289459678172420151 := by
  unfold tailWord_6293299
  simp only [CollatzResearch.WordTrace]
  refine ⟨229535471627460007744322951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153023647751640005162881967 229535471627460007744322951)
  ·
    refine ⟨344303207441190011616484427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229535471627460007744322951 344303207441190011616484427)
    ·
      refine ⟨516454811161785017424726641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344303207441190011616484427 516454811161785017424726641)
      ·
        refine ⟨387341108371338763068544981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516454811161785017424726641 387341108371338763068544981)
        ·
          refine ⟨9078307227453252259419023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 387341108371338763068544981 9078307227453252259419023)
          ·
            refine ⟨13617460841179878389128535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9078307227453252259419023 13617460841179878389128535)
            ·
              refine ⟨20426191261769817583692803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13617460841179878389128535 20426191261769817583692803)
              ·
                refine ⟨30639286892654726375539205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20426191261769817583692803 30639286892654726375539205)
                ·
                  refine ⟨5744866292372761195413601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30639286892654726375539205 5744866292372761195413601)
                  ·
                    refine ⟨4308649719279570896560201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744866292372761195413601 4308649719279570896560201)
                    ·
                      refine ⟨3231487289459678172420151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308649719279570896560201 3231487289459678172420151)
                      ·
                        rfl

theorem cell23_6293299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4, 2, 2].length) (baseStart_6293299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293299 prefixEnd_6293299 := by exact prefixLift 6293299
  have htrace : WordTrace (prefixWord ++ tailWord_6293299) baseStart_6293299 baseEnd_6293299 := by
    simpa [prefixWord, tailWord_6293299, baseEnd_6293299] using wordTrace_append hprefix tailTrace_6293299
  have hstable : (prefixWord ++ tailWord_6293299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293299).length < 2 ^ (prefixWord ++ tailWord_6293299).sum := by decide
  have hdescent : baseEnd_6293299 < baseStart_6293299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293315 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3]
def baseStart_6293315 : Nat := 118140960795 + 6293315 * 2 ^ 59
def prefixEnd_6293315 : Nat := 4983230072969 + 3 ^ 40 * 6293315 * 2
def baseEnd_6293315 : Nat := 3231495505150150109820077

theorem tailTrace_6293315 : CollatzResearch.WordTrace tailWord_6293315 prefixEnd_6293315 3231495505150150109820077 := by
  unfold tailWord_6293315
  simp only [CollatzResearch.WordTrace]
  refine ⟨229536055195402042476905399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153024036796934694984603599 229536055195402042476905399)
  ·
    refine ⟨344304082793103063715358099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229536055195402042476905399 344304082793103063715358099)
    ·
      refine ⟨516456124189654595573037149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344304082793103063715358099 516456124189654595573037149)
      ·
        refine ⟨193671046571120473339888931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516456124189654595573037149 193671046571120473339888931)
        ·
          refine ⟨290506569856680710009833397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193671046571120473339888931 290506569856680710009833397)
          ·
            refine ⟨27234990924063816563421881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290506569856680710009833397 27234990924063816563421881)
            ·
              refine ⟨20426243193047862422566411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27234990924063816563421881 20426243193047862422566411)
              ·
                refine ⟨30639364789571793633849617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20426243193047862422566411 30639364789571793633849617)
                ·
                  refine ⟨22979523592178845225387213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30639364789571793633849617 22979523592178845225387213)
                  ·
                    refine ⟨8617321347067066959520205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22979523592178845225387213 8617321347067066959520205)
                    ·
                      refine ⟨3231495505150150109820077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617321347067066959520205 3231495505150150109820077)
                      ·
                        rfl

theorem cell23_6293315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_6293315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293315 prefixEnd_6293315 := by exact prefixLift 6293315
  have htrace : WordTrace (prefixWord ++ tailWord_6293315) baseStart_6293315 baseEnd_6293315 := by
    simpa [prefixWord, tailWord_6293315, baseEnd_6293315] using wordTrace_append hprefix tailTrace_6293315
  have hstable : (prefixWord ++ tailWord_6293315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293315).length < 2 ^ (prefixWord ++ tailWord_6293315).sum := by decide
  have hdescent : baseEnd_6293315 < baseStart_6293315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293328 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_6293328 : Nat := 118140960795 + 6293328 * 2 ^ 59
def prefixEnd_6293328 : Nat := 4983230072969 + 3 ^ 40 * 6293328 * 2
def baseEnd_6293328 : Nat := 3231502180398658558957517

theorem tailTrace_6293328 : CollatzResearch.WordTrace tailWord_6293328 prefixEnd_6293328 3231502180398658558957517 := by
  unfold tailWord_6293328
  simp only [CollatzResearch.WordTrace]
  refine ⟨114768264672177472848564319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153024352896236630464752425 114768264672177472848564319)
  ·
    refine ⟨172152397008266209272846479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114768264672177472848564319 172152397008266209272846479)
    ·
      refine ⟨258228595512399313909269719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172152397008266209272846479 258228595512399313909269719)
      ·
        refine ⟨387342893268598970863904579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258228595512399313909269719 387342893268598970863904579)
        ·
          refine ⟨581014339902898456295856869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387342893268598970863904579 581014339902898456295856869)
          ·
            refine ⟨108940188731793460555473163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 581014339902898456295856869 108940188731793460555473163)
            ·
              refine ⟨163410283097690190833209745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108940188731793460555473163 163410283097690190833209745)
              ·
                refine ⟨122557712323267643124907309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163410283097690190833209745 122557712323267643124907309)
                ·
                  refine ⟨45959142121225366171840241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122557712323267643124907309 45959142121225366171840241)
                  ·
                    refine ⟨34469356590919024628880181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45959142121225366171840241 34469356590919024628880181)
                    ·
                      refine ⟨3231502180398658558957517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34469356590919024628880181 3231502180398658558957517)
                      ·
                        rfl

theorem cell23_6293328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_6293328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293328 prefixEnd_6293328 := by exact prefixLift 6293328
  have htrace : WordTrace (prefixWord ++ tailWord_6293328) baseStart_6293328 baseEnd_6293328 := by
    simpa [prefixWord, tailWord_6293328, baseEnd_6293328] using wordTrace_append hprefix tailTrace_6293328
  have hstable : (prefixWord ++ tailWord_6293328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293328).length < 2 ^ (prefixWord ++ tailWord_6293328).sum := by decide
  have hdescent : baseEnd_6293328 < baseStart_6293328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293368 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_6293368 : Nat := 118140960795 + 6293368 * 2 ^ 59
def prefixEnd_6293368 : Nat := 4983230072969 + 3 ^ 40 * 6293368 * 2
def baseEnd_6293368 : Nat := 3231522719624838402457333

theorem tailTrace_6293368 : CollatzResearch.WordTrace tailWord_6293368 prefixEnd_6293368 3231522719624838402457333 := by
  unfold tailWord_6293368
  simp only [CollatzResearch.WordTrace]
  refine ⟨114768994132105016264292379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153025325509473355019056505 114768994132105016264292379)
  ·
    refine ⟨172153491198157524396438569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114768994132105016264292379 172153491198157524396438569)
    ·
      refine ⟨129115118398618143297328927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172153491198157524396438569 129115118398618143297328927)
      ·
        refine ⟨193672677597927214945993391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129115118398618143297328927 193672677597927214945993391)
        ·
          refine ⟨290509016396890822418990087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193672677597927214945993391 290509016396890822418990087)
          ·
            refine ⟨435763524595336233628485131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290509016396890822418990087 435763524595336233628485131)
            ·
              refine ⟨653645286893004350442727697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435763524595336233628485131 653645286893004350442727697)
              ·
                refine ⟨490233965169753262832045773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653645286893004350442727697 490233965169753262832045773)
                ·
                  refine ⟨183837736938657473562017165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490233965169753262832045773 183837736938657473562017165)
                  ·
                    refine ⟨68939151351996552585756437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183837736938657473562017165 68939151351996552585756437)
                    ·
                      refine ⟨3231522719624838402457333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68939151351996552585756437 3231522719624838402457333)
                      ·
                        rfl

theorem cell23_6293368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_6293368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293368 prefixEnd_6293368 := by exact prefixLift 6293368
  have htrace : WordTrace (prefixWord ++ tailWord_6293368) baseStart_6293368 baseEnd_6293368 := by
    simpa [prefixWord, tailWord_6293368, baseEnd_6293368] using wordTrace_append hprefix tailTrace_6293368
  have hstable : (prefixWord ++ tailWord_6293368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293368).length < 2 ^ (prefixWord ++ tailWord_6293368).sum := by decide
  have hdescent : baseEnd_6293368 < baseStart_6293368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293375 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_6293375 : Nat := 118140960795 + 6293375 * 2 ^ 59
def prefixEnd_6293375 : Nat := 4983230072969 + 3 ^ 40 * 6293375 * 2
def baseEnd_6293375 : Nat := 3231526313989419875069801

theorem tailTrace_6293375 : CollatzResearch.WordTrace tailWord_6293375 prefixEnd_6293375 3231526313989419875069801 := by
  unfold tailWord_6293375
  simp only [CollatzResearch.WordTrace]
  refine ⟨229538243575184672724089579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153025495716789781816059719 229538243575184672724089579)
  ·
    refine ⟨344307365362777009086134369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229538243575184672724089579 344307365362777009086134369)
    ·
      refine ⟨258230524022082756814600777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344307365362777009086134369 258230524022082756814600777)
      ·
        refine ⟨193672893016562067610950583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258230524022082756814600777 193672893016562067610950583)
        ·
          refine ⟨290509339524843101416425875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193672893016562067610950583 290509339524843101416425875)
          ·
            refine ⟨435764009287264652124638813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290509339524843101416425875 435764009287264652124638813)
            ·
              refine ⟨163411503482724244546739555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435764009287264652124638813 163411503482724244546739555)
              ·
                refine ⟨245117255224086366820109333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163411503482724244546739555 245117255224086366820109333)
                ·
                  refine ⟨11489871338629048444692625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 245117255224086366820109333 11489871338629048444692625)
                  ·
                    refine ⟨8617403503971786333519469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11489871338629048444692625 8617403503971786333519469)
                    ·
                      refine ⟨3231526313989419875069801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617403503971786333519469 3231526313989419875069801)
                      ·
                        rfl

theorem cell23_6293375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_6293375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293375 prefixEnd_6293375 := by exact prefixLift 6293375
  have htrace : WordTrace (prefixWord ++ tailWord_6293375) baseStart_6293375 baseEnd_6293375 := by
    simpa [prefixWord, tailWord_6293375, baseEnd_6293375] using wordTrace_append hprefix tailTrace_6293375
  have hstable : (prefixWord ++ tailWord_6293375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293375).length < 2 ^ (prefixWord ++ tailWord_6293375).sum := by decide
  have hdescent : baseEnd_6293375 < baseStart_6293375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293412 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 6]
def baseStart_6293412 : Nat := 118140960795 + 6293412 * 2 ^ 59
def prefixEnd_6293412 : Nat := 4983230072969 + 3 ^ 40 * 6293412 * 2
def baseEnd_6293412 : Nat := 359060590308181803367459

theorem tailTrace_6293412 : CollatzResearch.WordTrace tailWord_6293412 prefixEnd_6293412 359060590308181803367459 := by
  unfold tailWord_6293412
  simp only [CollatzResearch.WordTrace]
  refine ⟨114769796538025314021593245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153026395384033752028790993 114769796538025314021593245)
  ·
    refine ⟨43038673701759492758097467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114769796538025314021593245 43038673701759492758097467)
    ·
      refine ⟨64558010552639239137146201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43038673701759492758097467 64558010552639239137146201)
      ·
        refine ⟨48418507914479429352859651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64558010552639239137146201 48418507914479429352859651)
        ·
          refine ⟨72627761871719144029289477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48418507914479429352859651 72627761871719144029289477)
          ·
            refine ⟨13617705350947339505491777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72627761871719144029289477 13617705350947339505491777)
            ·
              refine ⟨10213279013210504629118833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13617705350947339505491777 10213279013210504629118833)
              ·
                refine ⟨7659959259907878471839125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10213279013210504629118833 7659959259907878471839125)
                ·
                  refine ⟨359060590308181803367459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7659959259907878471839125 359060590308181803367459)
                  ·
                    rfl

theorem cell23_6293412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_6293412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293412 prefixEnd_6293412 := by exact prefixLift 6293412
  have htrace : WordTrace (prefixWord ++ tailWord_6293412) baseStart_6293412 baseEnd_6293412 := by
    simpa [prefixWord, tailWord_6293412, baseEnd_6293412] using wordTrace_append hprefix tailTrace_6293412
  have hstable : (prefixWord ++ tailWord_6293412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293412).length < 2 ^ (prefixWord ++ tailWord_6293412).sum := by decide
  have hdescent : baseEnd_6293412 < baseStart_6293412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293432 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_6293432 : Nat := 118140960795 + 6293432 * 2 ^ 59
def prefixEnd_6293432 : Nat := 4983230072969 + 3 ^ 40 * 6293432 * 2
def baseEnd_6293432 : Nat := 3231555582386726152057039

theorem tailTrace_6293432 : CollatzResearch.WordTrace tailWord_6293432 prefixEnd_6293432 3231555582386726152057039 := by
  unfold tailWord_6293432
  simp only [CollatzResearch.WordTrace]
  refine ⟨114770161267989085729457275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153026881690652114305943033 114770161267989085729457275)
  ·
    refine ⟨172155241901983628594185913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114770161267989085729457275 172155241901983628594185913)
    ·
      refine ⟨129116431426487721445639435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172155241901983628594185913 129116431426487721445639435)
      ·
        refine ⟨193674647139731582168459153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129116431426487721445639435 193674647139731582168459153)
        ·
          refine ⟨145255985354798686626344365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193674647139731582168459153 145255985354798686626344365)
          ·
            refine ⟨54470994508049507484879137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145255985354798686626344365 54470994508049507484879137)
            ·
              refine ⟨40853245881037130613659353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54470994508049507484879137 40853245881037130613659353)
              ·
                refine ⟨30639934410777847960244515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40853245881037130613659353 30639934410777847960244515)
                ·
                  refine ⟨45959901616166771940366773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30639934410777847960244515 45959901616166771940366773)
                  ·
                    refine ⟨4308740776515634869409385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45959901616166771940366773 4308740776515634869409385)
                    ·
                      refine ⟨3231555582386726152057039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308740776515634869409385 3231555582386726152057039)
                      ·
                        rfl

theorem cell23_6293432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_6293432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293432 prefixEnd_6293432 := by exact prefixLift 6293432
  have htrace : WordTrace (prefixWord ++ tailWord_6293432) baseStart_6293432 baseEnd_6293432 := by
    simpa [prefixWord, tailWord_6293432, baseEnd_6293432] using wordTrace_append hprefix tailTrace_6293432
  have hstable : (prefixWord ++ tailWord_6293432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293432).length < 2 ^ (prefixWord ++ tailWord_6293432).sum := by decide
  have hdescent : baseEnd_6293432 < baseStart_6293432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293455 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 1, 6]
def baseStart_6293455 : Nat := 118140960795 + 6293455 * 2 ^ 59
def prefixEnd_6293455 : Nat := 4983230072969 + 3 ^ 40 * 6293455 * 2
def baseEnd_6293455 : Nat := 1077189130813926520689811

theorem tailTrace_6293455 : CollatzResearch.WordTrace tailWord_6293455 prefixEnd_6293455 1077189130813926520689811 := by
  unfold tailWord_6293455
  simp only [CollatzResearch.WordTrace]
  refine ⟨229541161414894846387001819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153027440943263230924667879 229541161414894846387001819)
  ·
    refine ⟨344311742122342269580502729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229541161414894846387001819 344311742122342269580502729)
    ·
      refine ⟨258233806591756702185377047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344311742122342269580502729 258233806591756702185377047)
      ·
        refine ⟨387350709887635053278065571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258233806591756702185377047 387350709887635053278065571)
        ·
          refine ⟨581026064831452579917098357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387350709887635053278065571 581026064831452579917098357)
          ·
            refine ⟨54471193577948679367227971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 581026064831452579917098357 54471193577948679367227971)
            ·
              refine ⟨81706790366923019050841957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54471193577948679367227971 81706790366923019050841957)
              ·
                refine ⟨15320023193798066072032867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81706790366923019050841957 15320023193798066072032867)
                ·
                  refine ⟨22980034790697099108049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15320023193798066072032867 22980034790697099108049301)
                  ·
                    refine ⟨1077189130813926520689811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22980034790697099108049301 1077189130813926520689811)
                    ·
                      rfl

theorem cell23_6293455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_6293455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293455 prefixEnd_6293455 := by exact prefixLift 6293455
  have htrace : WordTrace (prefixWord ++ tailWord_6293455) baseStart_6293455 baseEnd_6293455 := by
    simpa [prefixWord, tailWord_6293455, baseEnd_6293455] using wordTrace_append hprefix tailTrace_6293455
  have hstable : (prefixWord ++ tailWord_6293455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293455).length < 2 ^ (prefixWord ++ tailWord_6293455).sum := by decide
  have hdescent : baseEnd_6293455 < baseStart_6293455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293482 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_6293482 : Nat := 118140960795 + 6293482 * 2 ^ 59
def prefixEnd_6293482 : Nat := 4983230072969 + 3 ^ 40 * 6293482 * 2
def baseEnd_6293482 : Nat := 3231581256419450956431809

theorem tailTrace_6293482 : CollatzResearch.WordTrace tailWord_6293482 prefixEnd_6293482 3231581256419450956431809 := by
  unfold tailWord_6293482
  simp only [CollatzResearch.WordTrace]
  refine ⟨57385536546449257499558675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153028097457198019998823133 57385536546449257499558675)
  ·
    refine ⟨86078304819673886249338013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57385536546449257499558675 86078304819673886249338013)
    ·
      refine ⟨32279364307377707343501755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86078304819673886249338013 32279364307377707343501755)
      ·
        refine ⟨48419046461066561015252633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32279364307377707343501755 48419046461066561015252633)
        ·
          refine ⟨36314284845799920761439475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48419046461066561015252633 36314284845799920761439475)
          ·
            refine ⟨54471427268699881142159213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36314284845799920761439475 54471427268699881142159213)
            ·
              refine ⟨20426785225762455428309705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54471427268699881142159213 20426785225762455428309705)
              ·
                refine ⟨15320088919321841571232279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20426785225762455428309705 15320088919321841571232279)
                ·
                  refine ⟨22980133378982762356848419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15320088919321841571232279 22980133378982762356848419)
                  ·
                    refine ⟨34470200068474143535272629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22980133378982762356848419 34470200068474143535272629)
                    ·
                      refine ⟨3231581256419450956431809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34470200068474143535272629 3231581256419450956431809)
                      ·
                        rfl

theorem cell23_6293482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_6293482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293482 prefixEnd_6293482 := by exact prefixLift 6293482
  have htrace : WordTrace (prefixWord ++ tailWord_6293482) baseStart_6293482 baseEnd_6293482 := by
    simpa [prefixWord, tailWord_6293482, baseEnd_6293482] using wordTrace_append hprefix tailTrace_6293482
  have hstable : (prefixWord ++ tailWord_6293482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293482).length < 2 ^ (prefixWord ++ tailWord_6293482).sum := by decide
  have hdescent : baseEnd_6293482 < baseStart_6293482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293489 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_6293489 : Nat := 118140960795 + 6293489 * 2 ^ 59
def prefixEnd_6293489 : Nat := 4983230072969 + 3 ^ 40 * 6293489 * 2
def baseEnd_6293489 : Nat := 1077194950261344143014759

theorem tailTrace_6293489 : CollatzResearch.WordTrace tailWord_6293489 prefixEnd_6293489 1077194950261344143014759 := by
  unfold tailWord_6293489
  simp only [CollatzResearch.WordTrace]
  refine ⟨229542401496771670193739521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153028267664514446795826347 229542401496771670193739521)
  ·
    refine ⟨172156801122578752645304641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229542401496771670193739521 172156801122578752645304641)
    ·
      refine ⟨129117600841934064483978481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172156801122578752645304641 129117600841934064483978481)
      ·
        refine ⟨96838200631450548362983861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129117600841934064483978481 96838200631450548362983861)
        ·
          refine ⟨9078581309198488909029737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96838200631450548362983861 9078581309198488909029737)
          ·
            refine ⟨6808935981898866681772303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078581309198488909029737 6808935981898866681772303)
            ·
              refine ⟨10213403972848300022658455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808935981898866681772303 10213403972848300022658455)
              ·
                refine ⟨15320105959272450033987683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10213403972848300022658455 15320105959272450033987683)
                ·
                  refine ⟨22980158938908675050981525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15320105959272450033987683 22980158938908675050981525)
                  ·
                    refine ⟨1077194950261344143014759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22980158938908675050981525 1077194950261344143014759)
                    ·
                      rfl

theorem cell23_6293489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_6293489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293489 prefixEnd_6293489 := by exact prefixLift 6293489
  have htrace : WordTrace (prefixWord ++ tailWord_6293489) baseStart_6293489 baseEnd_6293489 := by
    simpa [prefixWord, tailWord_6293489, baseEnd_6293489] using wordTrace_append hprefix tailTrace_6293489
  have hstable : (prefixWord ++ tailWord_6293489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293489).length < 2 ^ (prefixWord ++ tailWord_6293489).sum := by decide
  have hdescent : baseEnd_6293489 < baseStart_6293489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293512 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_6293512 : Nat := 118140960795 + 6293512 * 2 ^ 59
def prefixEnd_6293512 : Nat := 4983230072969 + 3 ^ 40 * 6293512 * 2
def baseEnd_6293512 : Nat := 3231596660839085839056671

theorem tailTrace_6293512 : CollatzResearch.WordTrace tailWord_6293512 prefixEnd_6293512 3231596660839085839056671 := by
  unfold tailWord_6293512
  simp only [CollatzResearch.WordTrace]
  refine ⟨114771620187844172560913395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153028826917125563414551193 114771620187844172560913395)
  ·
    refine ⟨172157430281766258841370093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114771620187844172560913395 172157430281766258841370093)
    ·
      refine ⟨64559036355662347065513785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172157430281766258841370093 64559036355662347065513785)
      ·
        refine ⟨48419277266746760299135339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64559036355662347065513785 48419277266746760299135339)
        ·
          refine ⟨72628915900120140448703009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48419277266746760299135339 72628915900120140448703009)
          ·
            refine ⟨54471686925090105336527257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72628915900120140448703009 54471686925090105336527257)
            ·
              refine ⟨40853765193817579002395443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54471686925090105336527257 40853765193817579002395443)
              ·
                refine ⟨61280647790726368503593165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40853765193817579002395443 61280647790726368503593165)
                ·
                  refine ⟨22980242921522388188847437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61280647790726368503593165 22980242921522388188847437)
                  ·
                    refine ⟨8617591095570895570817789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22980242921522388188847437 8617591095570895570817789)
                    ·
                      refine ⟨3231596660839085839056671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617591095570895570817789 3231596660839085839056671)
                      ·
                        rfl

theorem cell23_6293512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_6293512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293512 prefixEnd_6293512 := by exact prefixLift 6293512
  have htrace : WordTrace (prefixWord ++ tailWord_6293512) baseStart_6293512 baseEnd_6293512 := by
    simpa [prefixWord, tailWord_6293512, baseEnd_6293512] using wordTrace_append hprefix tailTrace_6293512
  have hstable : (prefixWord ++ tailWord_6293512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293512).length < 2 ^ (prefixWord ++ tailWord_6293512).sum := by decide
  have hdescent : baseEnd_6293512 < baseStart_6293512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293529 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 3]
def baseStart_6293529 : Nat := 118140960795 + 6293529 * 2 ^ 59
def prefixEnd_6293529 : Nat := 4983230072969 + 3 ^ 40 * 6293529 * 2
def baseEnd_6293529 : Nat := 3231605390010212272544093

theorem tailTrace_6293529 : CollatzResearch.WordTrace tailWord_6293529 prefixEnd_6293529 3231605390010212272544093 := by
  unfold tailWord_6293529
  simp only [CollatzResearch.WordTrace]
  refine ⟨229543860416626757025195641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153029240277751171350130427 229543860416626757025195641)
  ·
    refine ⟨172157895312470067768896731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229543860416626757025195641 172157895312470067768896731)
    ·
      refine ⟨258236842968705101653345097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172157895312470067768896731 258236842968705101653345097)
      ·
        refine ⟨193677632226528826240008823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258236842968705101653345097 193677632226528826240008823)
        ·
          refine ⟨290516448339793239360013235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193677632226528826240008823 290516448339793239360013235)
          ·
            refine ⟨435774672509689859040019853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290516448339793239360013235 435774672509689859040019853)
            ·
              refine ⟨163415502191133697140007445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435774672509689859040019853 163415502191133697140007445)
              ·
                refine ⟨7660101665209392053437849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163415502191133697140007445 7660101665209392053437849)
                ·
                  refine ⟨5745076248907044040078387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7660101665209392053437849 5745076248907044040078387)
                  ·
                    refine ⟨8617614373360566060117581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5745076248907044040078387 8617614373360566060117581)
                    ·
                      refine ⟨3231605390010212272544093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617614373360566060117581 3231605390010212272544093)
                      ·
                        rfl

theorem cell23_6293529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_6293529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293529 prefixEnd_6293529 := by exact prefixLift 6293529
  have htrace : WordTrace (prefixWord ++ tailWord_6293529) baseStart_6293529 baseEnd_6293529 := by
    simpa [prefixWord, tailWord_6293529, baseEnd_6293529] using wordTrace_append hprefix tailTrace_6293529
  have hstable : (prefixWord ++ tailWord_6293529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293529).length < 2 ^ (prefixWord ++ tailWord_6293529).sum := by decide
  have hdescent : baseEnd_6293529 < baseStart_6293529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293530 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2]
def baseStart_6293530 : Nat := 118140960795 + 6293530 * 2 ^ 59
def prefixEnd_6293530 : Nat := 4983230072969 + 3 ^ 40 * 6293530 * 2
def baseEnd_6293530 : Nat := 3231605903490866768631589

theorem tailTrace_6293530 : CollatzResearch.WordTrace tailWord_6293530 prefixEnd_6293530 3231605903490866768631589 := by
  unfold tailWord_6293530
  simp only [CollatzResearch.WordTrace]
  refine ⟨57385974222405783548995511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153029264593082089463988029 57385974222405783548995511)
  ·
    refine ⟨86078961333608675323493267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57385974222405783548995511 86078961333608675323493267)
    ·
      refine ⟨129118442000413012985239901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86078961333608675323493267 129118442000413012985239901)
      ·
        refine ⟨48419415750154879869464963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129118442000413012985239901 48419415750154879869464963)
        ·
          refine ⟨72629123625232319804197445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48419415750154879869464963 72629123625232319804197445)
          ·
            refine ⟨13617960679731059963287021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72629123625232319804197445 13617960679731059963287021)
            ·
              refine ⟨5106735254899147486232633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13617960679731059963287021 5106735254899147486232633)
              ·
                refine ⟨3830051441174360614674475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106735254899147486232633 3830051441174360614674475)
                ·
                  refine ⟨5745077161761540922011713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830051441174360614674475 5745077161761540922011713)
                  ·
                    refine ⟨4308807871321155691508785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745077161761540922011713 4308807871321155691508785)
                    ·
                      refine ⟨3231605903490866768631589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308807871321155691508785 3231605903490866768631589)
                      ·
                        rfl

theorem cell23_6293530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_6293530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293530 prefixEnd_6293530 := by exact prefixLift 6293530
  have htrace : WordTrace (prefixWord ++ tailWord_6293530) baseStart_6293530 baseEnd_6293530 := by
    simpa [prefixWord, tailWord_6293530, baseEnd_6293530] using wordTrace_append hprefix tailTrace_6293530
  have hstable : (prefixWord ++ tailWord_6293530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293530).length < 2 ^ (prefixWord ++ tailWord_6293530).sum := by decide
  have hdescent : baseEnd_6293530 < baseStart_6293530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293539 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 3, 3, 2]
def baseStart_6293539 : Nat := 118140960795 + 6293539 * 2 ^ 59
def prefixEnd_6293539 : Nat := 4983230072969 + 3 ^ 40 * 6293539 * 2
def baseEnd_6293539 : Nat := 3231610524816757233419047

theorem tailTrace_6293539 : CollatzResearch.WordTrace tailWord_6293539 prefixEnd_6293539 3231610524816757233419047 := by
  unfold tailWord_6293539
  simp only [CollatzResearch.WordTrace]
  refine ⟨229544225146590528733059671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153029483431060352488706447 229544225146590528733059671)
  ·
    refine ⟨344316337719885793099589507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229544225146590528733059671 344316337719885793099589507)
    ·
      refine ⟨516474506579828689649384261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344316337719885793099589507 516474506579828689649384261)
      ·
        refine ⟨96838969983717879309259549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516474506579828689649384261 96838969983717879309259549)
        ·
          refine ⟨36314613743894204740972331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96838969983717879309259549 36314613743894204740972331)
          ·
            refine ⟨54471920615841307111458497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36314613743894204740972331 54471920615841307111458497)
            ·
              refine ⟨40853940461880980333593873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54471920615841307111458497 40853940461880980333593873)
              ·
                refine ⟨30640455346410735250195405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40853940461880980333593873 30640455346410735250195405)
                ·
                  refine ⟨11490170754904025718823277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30640455346410735250195405 11490170754904025718823277)
                  ·
                    refine ⟨4308814033089009644558729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11490170754904025718823277 4308814033089009644558729)
                    ·
                      refine ⟨3231610524816757233419047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308814033089009644558729 3231610524816757233419047)
                      ·
                        rfl

theorem cell23_6293539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_6293539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293539 prefixEnd_6293539 := by exact prefixLift 6293539
  have htrace : WordTrace (prefixWord ++ tailWord_6293539) baseStart_6293539 baseEnd_6293539 := by
    simpa [prefixWord, tailWord_6293539, baseEnd_6293539] using wordTrace_append hprefix tailTrace_6293539
  have hstable : (prefixWord ++ tailWord_6293539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293539).length < 2 ^ (prefixWord ++ tailWord_6293539).sum := by decide
  have hdescent : baseEnd_6293539 < baseStart_6293539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293540 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_6293540 : Nat := 118140960795 + 6293540 * 2 ^ 59
def prefixEnd_6293540 : Nat := 4983230072969 + 3 ^ 40 * 6293540 * 2
def baseEnd_6293540 : Nat := 1077203679432470576502181

theorem tailTrace_6293540 : CollatzResearch.WordTrace tailWord_6293540 prefixEnd_6293540 1077203679432470576502181 := by
  unfold tailWord_6293540
  simp only [CollatzResearch.WordTrace]
  refine ⟨114772130809793452951923037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153029507746391270602564049 114772130809793452951923037)
  ·
    refine ⟨43039549053672544856971139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114772130809793452951923037 43039549053672544856971139)
    ·
      refine ⟨64559323580508817285456709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43039549053672544856971139 64559323580508817285456709)
      ·
        refine ⟨12104873171345403241023133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64559323580508817285456709 12104873171345403241023133)
        ·
          refine ⟨4539327439254526215383675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12104873171345403241023133 4539327439254526215383675)
          ·
            refine ⟨6808991158881789323075513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539327439254526215383675 6808991158881789323075513)
            ·
              refine ⟨5106743369161341992306635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6808991158881789323075513 5106743369161341992306635)
              ·
                refine ⟨7660115053742012988459953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106743369161341992306635 7660115053742012988459953)
                ·
                  refine ⟨5745086290306509741344965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7660115053742012988459953 5745086290306509741344965)
                  ·
                    refine ⟨1077203679432470576502181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5745086290306509741344965 1077203679432470576502181)
                    ·
                      rfl

theorem cell23_6293540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_6293540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293540 prefixEnd_6293540 := by exact prefixLift 6293540
  have htrace : WordTrace (prefixWord ++ tailWord_6293540) baseStart_6293540 baseEnd_6293540 := by
    simpa [prefixWord, tailWord_6293540, baseEnd_6293540] using wordTrace_append hprefix tailTrace_6293540
  have hstable : (prefixWord ++ tailWord_6293540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293540).length < 2 ^ (prefixWord ++ tailWord_6293540).sum := by decide
  have hdescent : baseEnd_6293540 < baseStart_6293540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293545 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_6293545 : Nat := 118140960795 + 6293545 * 2 ^ 59
def prefixEnd_6293545 : Nat := 4983230072969 + 3 ^ 40 * 6293545 * 2
def baseEnd_6293545 : Nat := 1077204535233561403314673

theorem tailTrace_6293545 : CollatzResearch.WordTrace tailWord_6293545 prefixEnd_6293545 1077204535233561403314673 := by
  unfold tailWord_6293545
  simp only [CollatzResearch.WordTrace]
  refine ⟨229544443984568791757778089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153029629323045861171852059 229544443984568791757778089)
  ·
    refine ⟨172158332988426593818333567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229544443984568791757778089 172158332988426593818333567)
    ·
      refine ⟨258237499482639890727500351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172158332988426593818333567 258237499482639890727500351)
      ·
        refine ⟨387356249223959836091250527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258237499482639890727500351 387356249223959836091250527)
        ·
          refine ⟨581034373835939754136875791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387356249223959836091250527 581034373835939754136875791)
          ·
            refine ⟨871551560753909631205313687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581034373835939754136875791 871551560753909631205313687)
            ·
              refine ⟨1307327341130864446807970531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871551560753909631205313687 1307327341130864446807970531)
              ·
                refine ⟨1960991011696296670211955797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307327341130864446807970531 1960991011696296670211955797)
                ·
                  refine ⟨22980363418315976604046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1960991011696296670211955797 22980363418315976604046357)
                  ·
                    refine ⟨1077204535233561403314673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22980363418315976604046357 1077204535233561403314673)
                    ·
                      rfl

theorem cell23_6293545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_6293545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293545 prefixEnd_6293545 := by exact prefixLift 6293545
  have htrace : WordTrace (prefixWord ++ tailWord_6293545) baseStart_6293545 baseEnd_6293545 := by
    simpa [prefixWord, tailWord_6293545, baseEnd_6293545] using wordTrace_append hprefix tailTrace_6293545
  have hstable : (prefixWord ++ tailWord_6293545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293545).length < 2 ^ (prefixWord ++ tailWord_6293545).sum := by decide
  have hdescent : baseEnd_6293545 < baseStart_6293545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293659 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 2, 4, 2]
def baseStart_6293659 : Nat := 118140960795 + 6293659 * 2 ^ 59
def prefixEnd_6293659 : Nat := 4983230072969 + 3 ^ 40 * 6293659 * 2
def baseEnd_6293659 : Nat := 3231672142495296763918495

theorem tailTrace_6293659 : CollatzResearch.WordTrace tailWord_6293659 prefixEnd_6293659 3231672142495296763918495 := by
  unfold tailWord_6293659
  simp only [CollatzResearch.WordTrace]
  refine ⟨229548601906155789227428031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153032401270770526151618687 229548601906155789227428031)
  ·
    refine ⟨344322902859233683841142047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229548601906155789227428031 344322902859233683841142047)
    ·
      refine ⟨516484354288850525761713071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344322902859233683841142047 516484354288850525761713071)
      ·
        refine ⟨774726531433275788642569607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516484354288850525761713071 774726531433275788642569607)
        ·
          refine ⟨1162089797149913682963854411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774726531433275788642569607 1162089797149913682963854411)
          ·
            refine ⟨1743134695724870524445781617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162089797149913682963854411 1743134695724870524445781617)
            ·
              refine ⟨1307351021793652893334336213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743134695724870524445781617 1307351021793652893334336213)
              ·
                refine ⟨30641039573288739687523505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1307351021793652893334336213 30641039573288739687523505)
                ·
                  refine ⟨22980779679966554765642629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30641039573288739687523505 22980779679966554765642629)
                  ·
                    refine ⟨4308896189993729018557993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22980779679966554765642629 4308896189993729018557993)
                    ·
                      refine ⟨3231672142495296763918495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308896189993729018557993 3231672142495296763918495)
                      ·
                        rfl

theorem cell23_6293659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 4, 2].length) (baseStart_6293659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293659 prefixEnd_6293659 := by exact prefixLift 6293659
  have htrace : WordTrace (prefixWord ++ tailWord_6293659) baseStart_6293659 baseEnd_6293659 := by
    simpa [prefixWord, tailWord_6293659, baseEnd_6293659] using wordTrace_append hprefix tailTrace_6293659
  have hstable : (prefixWord ++ tailWord_6293659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293659).length < 2 ^ (prefixWord ++ tailWord_6293659).sum := by decide
  have hdescent : baseEnd_6293659 < baseStart_6293659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293669 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_6293669 : Nat := 118140960795 + 6293669 * 2 ^ 59
def prefixEnd_6293669 : Nat := 4983230072969 + 3 ^ 40 * 6293669 * 2
def baseEnd_6293669 : Nat := 1077225759100613908264483

theorem tailTrace_6293669 : CollatzResearch.WordTrace tailWord_6293669 prefixEnd_6293669 1077225759100613908264483 := by
  unfold tailWord_6293669
  simp only [CollatzResearch.WordTrace]
  refine ⟨229548966636119560935292061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153032644424079707290194707 229548966636119560935292061)
  ·
    refine ⟨86080862488544835350734523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229548966636119560935292061 86080862488544835350734523)
    ·
      refine ⟨129121293732817253026101785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86080862488544835350734523 129121293732817253026101785)
      ·
        refine ⟨96840970299612939769576339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129121293732817253026101785 96840970299612939769576339)
        ·
          refine ⟨145261455449419409654364509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96840970299612939769576339 145261455449419409654364509)
          ·
            refine ⟨54473045793532278620386691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145261455449419409654364509 54473045793532278620386691)
            ·
              refine ⟨81709568690298417930580037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54473045793532278620386691 81709568690298417930580037)
              ·
                refine ⟨15320544129430953361983757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81709568690298417930580037 15320544129430953361983757)
                ·
                  refine ⟨5745204048536607510743909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15320544129430953361983757 5745204048536607510743909)
                  ·
                    refine ⟨1077225759100613908264483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5745204048536607510743909 1077225759100613908264483)
                    ·
                      rfl

theorem cell23_6293669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_6293669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293669 prefixEnd_6293669 := by exact prefixLift 6293669
  have htrace : WordTrace (prefixWord ++ tailWord_6293669) baseStart_6293669 baseEnd_6293669 := by
    simpa [prefixWord, tailWord_6293669, baseEnd_6293669] using wordTrace_append hprefix tailTrace_6293669
  have hstable : (prefixWord ++ tailWord_6293669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293669).length < 2 ^ (prefixWord ++ tailWord_6293669).sum := by decide
  have hdescent : baseEnd_6293669 < baseStart_6293669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293679 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_6293679 : Nat := 118140960795 + 6293679 * 2 ^ 59
def prefixEnd_6293679 : Nat := 4983230072969 + 3 ^ 40 * 6293679 * 2
def baseEnd_6293679 : Nat := 3231682412108386685668403

theorem tailTrace_6293679 : CollatzResearch.WordTrace tailWord_6293679 prefixEnd_6293679 3231682412108386685668403 := by
  unfold tailWord_6293679
  simp only [CollatzResearch.WordTrace]
  refine ⟨229549331366083332643156091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153032887577388888428770727 229549331366083332643156091)
  ·
    refine ⟨344323997049124998964734137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229549331366083332643156091 344323997049124998964734137)
    ·
      refine ⟨258242997786843749223550603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344323997049124998964734137 258242997786843749223550603)
      ·
        refine ⟨387364496680265623835325905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258242997786843749223550603 387364496680265623835325905)
        ·
          refine ⟨290523372510199217876494429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387364496680265623835325905 290523372510199217876494429)
          ·
            refine ⟨108946264691324706703685411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290523372510199217876494429 108946264691324706703685411)
            ·
              refine ⟨163419397036987060055528117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108946264691324706703685411 163419397036987060055528117)
              ·
                refine ⟨15320568472217536880205761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163419397036987060055528117 15320568472217536880205761)
                ·
                  refine ⟨11490426354163152660154321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15320568472217536880205761 11490426354163152660154321)
                  ·
                    refine ⟨8617819765622364495115741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11490426354163152660154321 8617819765622364495115741)
                    ·
                      refine ⟨3231682412108386685668403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617819765622364495115741 3231682412108386685668403)
                      ·
                        rfl

theorem cell23_6293679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_6293679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293679 prefixEnd_6293679 := by exact prefixLift 6293679
  have htrace : WordTrace (prefixWord ++ tailWord_6293679) baseStart_6293679 baseEnd_6293679 := by
    simpa [prefixWord, tailWord_6293679, baseEnd_6293679] using wordTrace_append hprefix tailTrace_6293679
  have hstable : (prefixWord ++ tailWord_6293679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293679).length < 2 ^ (prefixWord ++ tailWord_6293679).sum := by decide
  have hdescent : baseEnd_6293679 < baseStart_6293679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293682 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_6293682 : Nat := 118140960795 + 6293682 * 2 ^ 59
def prefixEnd_6293682 : Nat := 4983230072969 + 3 ^ 40 * 6293682 * 2
def baseEnd_6293682 : Nat := 359075994727816685992321

theorem tailTrace_6293682 : CollatzResearch.WordTrace tailWord_6293682 prefixEnd_6293682 359075994727816685992321 := by
  unfold tailWord_6293682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57387360196268116038878825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153032960523381642770343533 57387360196268116038878825)
  ·
    refine ⟨43040520147201087029159119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57387360196268116038878825 43040520147201087029159119)
    ·
      refine ⟨64560780220801630543738679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43040520147201087029159119 64560780220801630543738679)
      ·
        refine ⟨96841170331202445815608019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64560780220801630543738679 96841170331202445815608019)
        ·
          refine ⟨145261755496803668723412029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96841170331202445815608019 145261755496803668723412029)
          ·
            refine ⟨54473158311301375771279511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145261755496803668723412029 54473158311301375771279511)
            ·
              refine ⟨81709737466952063656919267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54473158311301375771279511 81709737466952063656919267)
              ·
                refine ⟨122564606200428095485378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81709737466952063656919267 122564606200428095485378901)
                ·
                  refine ⟨359075994727816685992321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122564606200428095485378901 359075994727816685992321)
                  ·
                    rfl

theorem cell23_6293682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_6293682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293682 prefixEnd_6293682 := by exact prefixLift 6293682
  have htrace : WordTrace (prefixWord ++ tailWord_6293682) baseStart_6293682 baseEnd_6293682 := by
    simpa [prefixWord, tailWord_6293682, baseEnd_6293682] using wordTrace_append hprefix tailTrace_6293682
  have hstable : (prefixWord ++ tailWord_6293682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293682).length < 2 ^ (prefixWord ++ tailWord_6293682).sum := by decide
  have hdescent : baseEnd_6293682 < baseStart_6293682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293696 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_6293696 : Nat := 118140960795 + 6293696 * 2 ^ 59
def prefixEnd_6293696 : Nat := 4983230072969 + 3 ^ 40 * 6293696 * 2
def baseEnd_6293696 : Nat := 3231691141279513119155825

theorem tailTrace_6293696 : CollatzResearch.WordTrace tailWord_6293696 prefixEnd_6293696 3231691141279513119155825 := by
  unfold tailWord_6293696
  simp only [CollatzResearch.WordTrace]
  refine ⟨114774975703510872273262471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153033300938014496364349961 114774975703510872273262471)
  ·
    refine ⟨172162463555266308409893707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114774975703510872273262471 172162463555266308409893707)
    ·
      refine ⟨258243695332899462614840561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172162463555266308409893707 258243695332899462614840561)
      ·
        refine ⟨193682771499674596961130421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258243695332899462614840561 193682771499674596961130421)
        ·
          refine ⟨18157759828094493465105977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193682771499674596961130421 18157759828094493465105977)
          ·
            refine ⟨13618319871070870098829483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18157759828094493465105977 13618319871070870098829483)
            ·
              refine ⟨20427479806606305148244225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13618319871070870098829483 20427479806606305148244225)
              ·
                refine ⟨15320609854954728861183169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20427479806606305148244225 15320609854954728861183169)
                ·
                  refine ⟨11490457391216046645887377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15320609854954728861183169 11490457391216046645887377)
                  ·
                    refine ⟨8617843043412034984415533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11490457391216046645887377 8617843043412034984415533)
                    ·
                      refine ⟨3231691141279513119155825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617843043412034984415533 3231691141279513119155825)
                      ·
                        rfl

theorem cell23_6293696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_6293696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293696 prefixEnd_6293696 := by exact prefixLift 6293696
  have htrace : WordTrace (prefixWord ++ tailWord_6293696) baseStart_6293696 baseEnd_6293696 := by
    simpa [prefixWord, tailWord_6293696, baseEnd_6293696] using wordTrace_append hprefix tailTrace_6293696
  have hstable : (prefixWord ++ tailWord_6293696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293696).length < 2 ^ (prefixWord ++ tailWord_6293696).sum := by decide
  have hdescent : baseEnd_6293696 < baseStart_6293696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293729 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_6293729 : Nat := 118140960795 + 6293729 * 2 ^ 59
def prefixEnd_6293729 : Nat := 4983230072969 + 3 ^ 40 * 6293729 * 2
def baseEnd_6293729 : Nat := 1077236028713703830014391

theorem tailTrace_6293729 : CollatzResearch.WordTrace tailWord_6293729 prefixEnd_6293729 1077236028713703830014391 := by
  unfold tailWord_6293729
  simp only [CollatzResearch.WordTrace]
  refine ⟨229551155015902191182476241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153034103343934794121650827 229551155015902191182476241)
  ·
    refine ⟨172163366261926643386857181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229551155015902191182476241 172163366261926643386857181)
    ·
      refine ⟨64561262348222491270071443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172163366261926643386857181 64561262348222491270071443)
      ·
        refine ⟨96841893522333736905107165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64561262348222491270071443 96841893522333736905107165)
        ·
          refine ⟨36315710070875151339415187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96841893522333736905107165 36315710070875151339415187)
          ·
            refine ⟨54473565106312727009122781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36315710070875151339415187 54473565106312727009122781)
            ·
              refine ⟨20427586914867272628421043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54473565106312727009122781 20427586914867272628421043)
              ·
                refine ⟨30641380372300908942631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20427586914867272628421043 30641380372300908942631565)
                ·
                  refine ⟨11490517639612840853486837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30641380372300908942631565 11490517639612840853486837)
                  ·
                    refine ⟨1077236028713703830014391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11490517639612840853486837 1077236028713703830014391)
                    ·
                      rfl

theorem cell23_6293729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_6293729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293729 prefixEnd_6293729 := by exact prefixLift 6293729
  have htrace : WordTrace (prefixWord ++ tailWord_6293729) baseStart_6293729 baseEnd_6293729 := by
    simpa [prefixWord, tailWord_6293729, baseEnd_6293729] using wordTrace_append hprefix tailTrace_6293729
  have hstable : (prefixWord ++ tailWord_6293729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293729).length < 2 ^ (prefixWord ++ tailWord_6293729).sum := by decide
  have hdescent : baseEnd_6293729 < baseStart_6293729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293760 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 1, 1, 3]
def baseStart_6293760 : Nat := 118140960795 + 6293760 * 2 ^ 59
def prefixEnd_6293760 : Nat := 4983230072969 + 3 ^ 40 * 6293760 * 2
def baseEnd_6293760 : Nat := 3231724004041400868755531

theorem tailTrace_6293760 : CollatzResearch.WordTrace tailWord_6293760 prefixEnd_6293760 3231724004041400868755531 := by
  unfold tailWord_6293760
  simp only [CollatzResearch.WordTrace]
  refine ⟨114776142839394941738427367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153034857119193255651236489 114776142839394941738427367)
  ·
    refine ⟨172164214259092412607641051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114776142839394941738427367 172164214259092412607641051)
    ·
      refine ⟨258246321388638618911461577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172164214259092412607641051 258246321388638618911461577)
      ·
        refine ⟨193684741041478964183596183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258246321388638618911461577 193684741041478964183596183)
        ·
          refine ⟨290527111562218446275394275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193684741041478964183596183 290527111562218446275394275)
          ·
            refine ⟨435790667343327669413091413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290527111562218446275394275 435790667343327669413091413)
            ·
              refine ⟨5106921882929621125934665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 435790667343327669413091413 5106921882929621125934665)
              ·
                refine ⟨3830191412197215844450999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106921882929621125934665 3830191412197215844450999)
                ·
                  refine ⟨5745287118295823766676499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830191412197215844450999 5745287118295823766676499)
                  ·
                    refine ⟨8617930677443735650014749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5745287118295823766676499 8617930677443735650014749)
                    ·
                      refine ⟨3231724004041400868755531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8617930677443735650014749 3231724004041400868755531)
                      ·
                        rfl

theorem cell23_6293760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_6293760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293760 prefixEnd_6293760 := by exact prefixLift 6293760
  have htrace : WordTrace (prefixWord ++ tailWord_6293760) baseStart_6293760 baseEnd_6293760 := by
    simpa [prefixWord, tailWord_6293760, baseEnd_6293760] using wordTrace_append hprefix tailTrace_6293760
  have hstable : (prefixWord ++ tailWord_6293760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293760).length < 2 ^ (prefixWord ++ tailWord_6293760).sum := by decide
  have hdescent : baseEnd_6293760 < baseStart_6293760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293783 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_6293783 : Nat := 118140960795 + 6293783 * 2 ^ 59
def prefixEnd_6293783 : Nat := 4983230072969 + 3 ^ 40 * 6293783 * 2
def baseEnd_6293783 : Nat := 3231735814096454278767925

theorem tailTrace_6293783 : CollatzResearch.WordTrace tailWord_6293783 prefixEnd_6293783 3231735814096454278767925 := by
  unfold tailWord_6293783
  simp only [CollatzResearch.WordTrace]
  refine ⟨229553124557706558404942003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153035416371804372269961335 229553124557706558404942003)
  ·
    refine ⟨344329686836559837607413005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229553124557706558404942003 344329686836559837607413005)
    ·
      refine ⟨129123632563709939102779877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344329686836559837607413005 129123632563709939102779877)
      ·
        refine ⟨24210681105695613581771227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129123632563709939102779877 24210681105695613581771227)
        ·
          refine ⟨36316021658543420372656841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24210681105695613581771227 36316021658543420372656841)
          ·
            refine ⟨27237016243907565279492631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36316021658543420372656841 27237016243907565279492631)
            ·
              refine ⟨40855524365861347919238947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27237016243907565279492631 40855524365861347919238947)
              ·
                refine ⟨61283286548792021878858421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40855524365861347919238947 61283286548792021878858421)
                ·
                  refine ⟨5745308113949252051142977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61283286548792021878858421 5745308113949252051142977)
                  ·
                    refine ⟨4308981085461939038357233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745308113949252051142977 4308981085461939038357233)
                    ·
                      refine ⟨3231735814096454278767925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4308981085461939038357233 3231735814096454278767925)
                      ·
                        rfl

theorem cell23_6293783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_6293783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293783 prefixEnd_6293783 := by exact prefixLift 6293783
  have htrace : WordTrace (prefixWord ++ tailWord_6293783) baseStart_6293783 baseEnd_6293783 := by
    simpa [prefixWord, tailWord_6293783, baseEnd_6293783] using wordTrace_append hprefix tailTrace_6293783
  have hstable : (prefixWord ++ tailWord_6293783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293783).length < 2 ^ (prefixWord ++ tailWord_6293783).sum := by decide
  have hdescent : baseEnd_6293783 < baseStart_6293783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293796 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_6293796 : Nat := 118140960795 + 6293796 * 2 ^ 59
def prefixEnd_6293796 : Nat := 4983230072969 + 3 ^ 40 * 6293796 * 2
def baseEnd_6293796 : Nat := 3231742489344962727905365

theorem tailTrace_6293796 : CollatzResearch.WordTrace tailWord_6293796 prefixEnd_6293796 3231742489344962727905365 := by
  unfold tailWord_6293796
  simp only [CollatzResearch.WordTrace]
  refine ⟨114776799353329730812582621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153035732471106307750110161 114776799353329730812582621)
  ·
    refine ⟨43041299757498649054718483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114776799353329730812582621 43041299757498649054718483)
    ·
      refine ⟨64561949636247973582077725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43041299757498649054718483 64561949636247973582077725)
      ·
        refine ⟨24210731113592990093279147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64561949636247973582077725 24210731113592990093279147)
        ·
          refine ⟨36316096670389485139918721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24210731113592990093279147 36316096670389485139918721)
          ·
            refine ⟨27237072502792113854939041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36316096670389485139918721 27237072502792113854939041)
            ·
              refine ⟨20427804377094085391204281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27237072502792113854939041 20427804377094085391204281)
              ·
                refine ⟨15320853282820564043403211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20427804377094085391204281 15320853282820564043403211)
                ·
                  refine ⟨22981279924230846065104817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15320853282820564043403211 22981279924230846065104817)
                  ·
                    refine ⟨17235959943173134548828613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22981279924230846065104817 17235959943173134548828613)
                    ·
                      refine ⟨3231742489344962727905365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17235959943173134548828613 3231742489344962727905365)
                      ·
                        rfl

theorem cell23_6293796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_6293796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293796 prefixEnd_6293796 := by exact prefixLift 6293796
  have htrace : WordTrace (prefixWord ++ tailWord_6293796) baseStart_6293796 baseEnd_6293796 := by
    simpa [prefixWord, tailWord_6293796, baseEnd_6293796] using wordTrace_append hprefix tailTrace_6293796
  have hstable : (prefixWord ++ tailWord_6293796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293796).length < 2 ^ (prefixWord ++ tailWord_6293796).sum := by decide
  have hdescent : baseEnd_6293796 < baseStart_6293796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293810 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_6293810 : Nat := 118140960795 + 6293810 * 2 ^ 59
def prefixEnd_6293810 : Nat := 4983230072969 + 3 ^ 40 * 6293810 * 2
def baseEnd_6293810 : Nat := 1077249892691375224376767

theorem tailTrace_6293810 : CollatzResearch.WordTrace tailWord_6293810 prefixEnd_6293810 1077249892691375224376767 := by
  unfold tailWord_6293810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57388527332152185504043721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153036072885739161344116589 57388527332152185504043721)
  ·
    refine ⟨43041395499114139128032791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57388527332152185504043721 43041395499114139128032791)
    ·
      refine ⟨64562093248671208692049187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43041395499114139128032791 64562093248671208692049187)
      ·
        refine ⟨96843139873006813038073781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64562093248671208692049187 96843139873006813038073781)
        ·
          refine ⟨9079044363094388722319417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96843139873006813038073781 9079044363094388722319417)
          ·
            refine ⟨6809283272320791541739563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9079044363094388722319417 6809283272320791541739563)
            ·
              refine ⟨10213924908481187312609345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809283272320791541739563 10213924908481187312609345)
              ·
                refine ⟨7660443681360890484457009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10213924908481187312609345 7660443681360890484457009)
                ·
                  refine ⟨5745332761020667863342757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7660443681360890484457009 5745332761020667863342757)
                  ·
                    refine ⟨1077249892691375224376767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5745332761020667863342757 1077249892691375224376767)
                    ·
                      rfl

theorem cell23_6293810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_6293810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293810 prefixEnd_6293810 := by exact prefixLift 6293810
  have htrace : WordTrace (prefixWord ++ tailWord_6293810) baseStart_6293810 baseEnd_6293810 := by
    simpa [prefixWord, tailWord_6293810, baseEnd_6293810] using wordTrace_append hprefix tailTrace_6293810
  have hstable : (prefixWord ++ tailWord_6293810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293810).length < 2 ^ (prefixWord ++ tailWord_6293810).sum := by decide
  have hdescent : baseEnd_6293810 < baseStart_6293810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293817 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6293817 : Nat := 118140960795 + 6293817 * 2 ^ 59
def prefixEnd_6293817 : Nat := 4983230072969 + 3 ^ 40 * 6293817 * 2
def baseEnd_6293817 : Nat := 3231753272438707145742769

theorem tailTrace_6293817 : CollatzResearch.WordTrace tailWord_6293817 prefixEnd_6293817 3231753272438707145742769 := by
  unfold tailWord_6293817
  simp only [CollatzResearch.WordTrace]
  refine ⟨229554364639583382211679705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153036243093055588141119803 229554364639583382211679705)
  ·
    refine ⟨172165773479687536658759779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229554364639583382211679705 172165773479687536658759779)
    ·
      refine ⟨258248660219531304988139669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172165773479687536658759779 258248660219531304988139669)
      ·
        refine ⟨12105405947790529921319047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 258248660219531304988139669 12105405947790529921319047)
        ·
          refine ⟨18158108921685794881978571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12105405947790529921319047 18158108921685794881978571)
          ·
            refine ⟨27237163382528692322967857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18158108921685794881978571 27237163382528692322967857)
            ·
              refine ⟨20427872536896519242225893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27237163382528692322967857 20427872536896519242225893)
              ·
                refine ⟨3830226100668097357917355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20427872536896519242225893 3830226100668097357917355)
                ·
                  refine ⟨5745339151002146036876033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830226100668097357917355 5745339151002146036876033)
                  ·
                    refine ⟨4309004363251609527657025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745339151002146036876033 4309004363251609527657025)
                    ·
                      refine ⟨3231753272438707145742769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309004363251609527657025 3231753272438707145742769)
                      ·
                        rfl

theorem cell23_6293817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6293817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293817 prefixEnd_6293817 := by exact prefixLift 6293817
  have htrace : WordTrace (prefixWord ++ tailWord_6293817) baseStart_6293817 baseEnd_6293817 := by
    simpa [prefixWord, tailWord_6293817, baseEnd_6293817] using wordTrace_append hprefix tailTrace_6293817
  have hstable : (prefixWord ++ tailWord_6293817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293817).length < 2 ^ (prefixWord ++ tailWord_6293817).sum := by decide
  have hdescent : baseEnd_6293817 < baseStart_6293817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293854 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6293854 : Nat := 118140960795 + 6293854 * 2 ^ 59
def prefixEnd_6293854 : Nat := 4983230072969 + 3 ^ 40 * 6293854 * 2
def baseEnd_6293854 : Nat := 3231772271222923500980099

theorem tailTrace_6293854 : CollatzResearch.WordTrace tailWord_6293854 prefixEnd_6293854 3231772271222923500980099 := by
  unfold tailWord_6293854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28694464267556167191347077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153037142760299558353851077 28694464267556167191347077)
  ·
    refine ⟨5380212050166781348377577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28694464267556167191347077 5380212050166781348377577)
    ·
      refine ⟨4035159037625086011283183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5380212050166781348377577 4035159037625086011283183)
      ·
        refine ⟨6052738556437629016924775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035159037625086011283183 6052738556437629016924775)
        ·
          refine ⟨9079107834656443525387163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6052738556437629016924775 9079107834656443525387163)
          ·
            refine ⟨13618661751984665288080745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079107834656443525387163 13618661751984665288080745)
            ·
              refine ⟨10213996313988498966060559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13618661751984665288080745 10213996313988498966060559)
              ·
                refine ⟨15320994470982748449090839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10213996313988498966060559 15320994470982748449090839)
                ·
                  refine ⟨22981491706474122673636259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15320994470982748449090839 22981491706474122673636259)
                  ·
                    refine ⟨34472237559711184010454389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22981491706474122673636259 34472237559711184010454389)
                    ·
                      refine ⟨3231772271222923500980099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34472237559711184010454389 3231772271222923500980099)
                      ·
                        rfl

theorem cell23_6293854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6293854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293854 prefixEnd_6293854 := by exact prefixLift 6293854
  have htrace : WordTrace (prefixWord ++ tailWord_6293854) baseStart_6293854 baseEnd_6293854 := by
    simpa [prefixWord, tailWord_6293854, baseEnd_6293854] using wordTrace_append hprefix tailTrace_6293854
  have hstable : (prefixWord ++ tailWord_6293854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293854).length < 2 ^ (prefixWord ++ tailWord_6293854).sum := by decide
  have hdescent : baseEnd_6293854 < baseStart_6293854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293879 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 7]
def baseStart_6293879 : Nat := 118140960795 + 6293879 * 2 ^ 59
def prefixEnd_6293879 : Nat := 4983230072969 + 3 ^ 40 * 6293879 * 2
def baseEnd_6293879 : Nat := 359087234248809544796387

theorem tailTrace_6293879 : CollatzResearch.WordTrace tailWord_6293879 prefixEnd_6293879 359087234248809544796387 := by
  unfold tailWord_6293879
  simp only [CollatzResearch.WordTrace]
  refine ⟨229556625965358766800436691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153037750643572511200291127 229556625965358766800436691)
  ·
    refine ⟨344334938948038150200655037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229556625965358766800436691 344334938948038150200655037)
    ·
      refine ⟨129125602105514306325245639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344334938948038150200655037 129125602105514306325245639)
      ·
        refine ⟨193688403158271459487868459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129125602105514306325245639 193688403158271459487868459)
        ·
          refine ⟨290532604737407189231802689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193688403158271459487868459 290532604737407189231802689)
          ·
            refine ⟨217899453553055391923852017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290532604737407189231802689 217899453553055391923852017)
            ·
              refine ⟨163424590164791543942889013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217899453553055391923852017 163424590164791543942889013)
              ·
                refine ⟨15321055327949207244645845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163424590164791543942889013 15321055327949207244645845)
                ·
                  refine ⟨359087234248809544796387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15321055327949207244645845 359087234248809544796387)
                  ·
                    rfl

theorem cell23_6293879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 7].length) (baseStart_6293879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293879 prefixEnd_6293879 := by exact prefixLift 6293879
  have htrace : WordTrace (prefixWord ++ tailWord_6293879) baseStart_6293879 baseEnd_6293879 := by
    simpa [prefixWord, tailWord_6293879, baseEnd_6293879] using wordTrace_append hprefix tailTrace_6293879
  have hstable : (prefixWord ++ tailWord_6293879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293879).length < 2 ^ (prefixWord ++ tailWord_6293879).sum := by decide
  have hdescent : baseEnd_6293879 < baseStart_6293879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293939 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 8]
def baseStart_6293939 : Nat := 118140960795 + 6293939 * 2 ^ 59
def prefixEnd_6293939 : Nat := 4983230072969 + 3 ^ 40 * 6293939 * 2
def baseEnd_6293939 : Nat := 1077271972359518556139069

theorem tailTrace_6293939 : CollatzResearch.WordTrace tailWord_6293939 prefixEnd_6293939 1077271972359518556139069 := by
  unfold tailWord_6293939
  simp only [CollatzResearch.WordTrace]
  refine ⟨229558814345141397047620871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153039209563427598031747247 229558814345141397047620871)
  ·
    refine ⟨344338221517712095571431307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229558814345141397047620871 344338221517712095571431307)
    ·
      refine ⟨516507332276568143357146961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344338221517712095571431307 516507332276568143357146961)
      ·
        refine ⟨387380499207426107517860221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516507332276568143357146961 387380499207426107517860221)
        ·
          refine ⟨145267687202784790319197583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387380499207426107517860221 145267687202784790319197583)
          ·
            refine ⟨217901530804177185478796375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145267687202784790319197583 217901530804177185478796375)
            ·
              refine ⟨326852296206265778218194563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217901530804177185478796375 326852296206265778218194563)
              ·
                refine ⟨490278444309398667327291845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326852296206265778218194563 490278444309398667327291845)
                ·
                  refine ⟨91927208308012250123867221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490278444309398667327291845 91927208308012250123867221)
                  ·
                    refine ⟨1077271972359518556139069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91927208308012250123867221 1077271972359518556139069)
                    ·
                      rfl

theorem cell23_6293939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_6293939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293939 prefixEnd_6293939 := by exact prefixLift 6293939
  have htrace : WordTrace (prefixWord ++ tailWord_6293939) baseStart_6293939 baseEnd_6293939 := by
    simpa [prefixWord, tailWord_6293939, baseEnd_6293939] using wordTrace_append hprefix tailTrace_6293939
  have hstable : (prefixWord ++ tailWord_6293939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293939).length < 2 ^ (prefixWord ++ tailWord_6293939).sum := by decide
  have hdescent : baseEnd_6293939 < baseStart_6293939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6293946 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_6293946 : Nat := 118140960795 + 6293946 * 2 ^ 59
def prefixEnd_6293946 : Nat := 4983230072969 + 3 ^ 40 * 6293946 * 2
def baseEnd_6293946 : Nat := 3231819511443137141029675

theorem tailTrace_6293946 : CollatzResearch.WordTrace tailWord_6293946 prefixEnd_6293946 3231819511443137141029675 := by
  unfold tailWord_6293946
  simp only [CollatzResearch.WordTrace]
  refine ⟨57389767414029009310781423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153039379770744024828750461 57389767414029009310781423)
  ·
    refine ⟨86084651121043513966172135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57389767414029009310781423 86084651121043513966172135)
    ·
      refine ⟨129126976681565270949258203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86084651121043513966172135 129126976681565270949258203)
      ·
        refine ⟨193690465022347906423887305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129126976681565270949258203 193690465022347906423887305)
        ·
          refine ⟨145267848766760929817915479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193690465022347906423887305 145267848766760929817915479)
          ·
            refine ⟨217901773150141394726873219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145267848766760929817915479 217901773150141394726873219)
            ·
              refine ⟨326852659725212092090309829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217901773150141394726873219 326852659725212092090309829)
              ·
                refine ⟨61284873698477267266933093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326852659725212092090309829 61284873698477267266933093)
                ·
                  refine ⟨11490913818464487612549955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61284873698477267266933093 11490913818464487612549955)
                  ·
                    refine ⟨17236370727696731418824933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11490913818464487612549955 17236370727696731418824933)
                    ·
                      refine ⟨3231819511443137141029675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17236370727696731418824933 3231819511443137141029675)
                      ·
                        rfl

theorem cell23_6293946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_6293946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6293946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6293946 prefixEnd_6293946 := by exact prefixLift 6293946
  have htrace : WordTrace (prefixWord ++ tailWord_6293946) baseStart_6293946 baseEnd_6293946 := by
    simpa [prefixWord, tailWord_6293946, baseEnd_6293946] using wordTrace_append hprefix tailTrace_6293946
  have hstable : (prefixWord ++ tailWord_6293946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6293946).length < 2 ^ (prefixWord ++ tailWord_6293946).sum := by decide
  have hdescent : baseEnd_6293946 < baseStart_6293946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6293946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294003 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 6]
def baseStart_6294003 : Nat := 118140960795 + 6294003 * 2 ^ 59
def prefixEnd_6294003 : Nat := 4983230072969 + 3 ^ 40 * 6294003 * 2
def baseEnd_6294003 : Nat := 359094308871160379779657

theorem tailTrace_6294003 : CollatzResearch.WordTrace tailWord_6294003 prefixEnd_6294003 359094308871160379779657 := by
  unfold tailWord_6294003
  simp only [CollatzResearch.WordTrace]
  refine ⟨229561148616909535977950663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153040765744606357318633775 229561148616909535977950663)
  ·
    refine ⟨344341722925364303966925995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229561148616909535977950663 344341722925364303966925995)
    ·
      refine ⟨516512584388046455950388993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344341722925364303966925995 516512584388046455950388993)
      ·
        refine ⟨387384438291034841962791745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516512584388046455950388993 387384438291034841962791745)
        ·
          refine ⟨290538328718276131472093809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387384438291034841962791745 290538328718276131472093809)
          ·
            refine ⟨217903746538707098604070357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290538328718276131472093809 217903746538707098604070357)
            ·
              refine ⟨5107119059500947623532899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 217903746538707098604070357 5107119059500947623532899)
              ·
                refine ⟨7660678589251421435299349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107119059500947623532899 7660678589251421435299349)
                ·
                  refine ⟨359094308871160379779657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7660678589251421435299349 359094308871160379779657)
                  ·
                    rfl

theorem cell23_6294003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 6].length) (baseStart_6294003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294003 prefixEnd_6294003 := by exact prefixLift 6294003
  have htrace : WordTrace (prefixWord ++ tailWord_6294003) baseStart_6294003 baseEnd_6294003 := by
    simpa [prefixWord, tailWord_6294003, baseEnd_6294003] using wordTrace_append hprefix tailTrace_6294003
  have hstable : (prefixWord ++ tailWord_6294003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294003).length < 2 ^ (prefixWord ++ tailWord_6294003).sum := by decide
  have hdescent : baseEnd_6294003 < baseStart_6294003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294040 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6294040 : Nat := 118140960795 + 6294040 * 2 ^ 59
def prefixEnd_6294040 : Nat := 4983230072969 + 3 ^ 40 * 6294040 * 2
def baseEnd_6294040 : Nat := 3231867778624659773254243

theorem tailTrace_6294040 : CollatzResearch.WordTrace tailWord_6294040 prefixEnd_6294040 3231867778624659773254243 := by
  unfold tailWord_6294040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114781249058887745648523787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153041665411850327531365049 114781249058887745648523787)
  ·
    refine ⟨172171873588331618472785681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114781249058887745648523787 172171873588331618472785681)
    ·
      refine ⟨129128905191248713854589261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172171873588331618472785681 129128905191248713854589261)
      ·
        refine ⟨48423339446718267695470973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129128905191248713854589261 48423339446718267695470973)
        ·
          refine ⟨18158752292519350385801615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48423339446718267695470973 18158752292519350385801615)
          ·
            refine ⟨27238128438779025578702423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18158752292519350385801615 27238128438779025578702423)
            ·
              refine ⟨40857192658168538368053635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27238128438779025578702423 40857192658168538368053635)
              ·
                refine ⟨61285788987252807552080453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40857192658168538368053635 61285788987252807552080453)
                ·
                  refine ⟨11491085435109901416015085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61285788987252807552080453 11491085435109901416015085)
                  ·
                    refine ⟨4309157038166213031005657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11491085435109901416015085 4309157038166213031005657)
                    ·
                      refine ⟨3231867778624659773254243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309157038166213031005657 3231867778624659773254243)
                      ·
                        rfl

theorem cell23_6294040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6294040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294040 prefixEnd_6294040 := by exact prefixLift 6294040
  have htrace : WordTrace (prefixWord ++ tailWord_6294040) baseStart_6294040 baseEnd_6294040 := by
    simpa [prefixWord, tailWord_6294040, baseEnd_6294040] using wordTrace_append hprefix tailTrace_6294040
  have hstable : (prefixWord ++ tailWord_6294040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294040).length < 2 ^ (prefixWord ++ tailWord_6294040).sum := by decide
  have hdescent : baseEnd_6294040 < baseStart_6294040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294087 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_6294087 : Nat := 118140960795 + 6294087 * 2 ^ 59
def prefixEnd_6294087 : Nat := 4983230072969 + 3 ^ 40 * 6294087 * 2
def baseEnd_6294087 : Nat := 3231891912215421089366527

theorem tailTrace_6294087 : CollatzResearch.WordTrace tailWord_6294087 prefixEnd_6294087 3231891912215421089366527 := by
  unfold tailWord_6294087
  simp only [CollatzResearch.WordTrace]
  refine ⟨229564212348605218324008515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153042808232403478882672343 229564212348605218324008515)
  ·
    refine ⟨344346318522907827486012773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229564212348605218324008515 344346318522907827486012773)
    ·
      refine ⟨64564934723045217653627395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344346318522907827486012773 64564934723045217653627395)
      ·
        refine ⟨96847402084567826480441093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64564934723045217653627395 96847402084567826480441093)
        ·
          refine ⟨18158887890856467465082705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96847402084567826480441093 18158887890856467465082705)
          ·
            refine ⟨13619165918142350598812029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18158887890856467465082705 13619165918142350598812029)
            ·
              refine ⟨5107187219303381474554511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13619165918142350598812029 5107187219303381474554511)
              ·
                refine ⟨7660780828955072211831767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107187219303381474554511 7660780828955072211831767)
                ·
                  refine ⟨11491171243432608317747651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660780828955072211831767 11491171243432608317747651)
                  ·
                    refine ⟨17236756865148912476621477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11491171243432608317747651 17236756865148912476621477)
                    ·
                      refine ⟨3231891912215421089366527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17236756865148912476621477 3231891912215421089366527)
                      ·
                        rfl

theorem cell23_6294087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_6294087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294087 prefixEnd_6294087 := by exact prefixLift 6294087
  have htrace : WordTrace (prefixWord ++ tailWord_6294087) baseStart_6294087 baseEnd_6294087 := by
    simpa [prefixWord, tailWord_6294087, baseEnd_6294087] using wordTrace_append hprefix tailTrace_6294087
  have hstable : (prefixWord ++ tailWord_6294087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294087).length < 2 ^ (prefixWord ++ tailWord_6294087).sum := by decide
  have hdescent : baseEnd_6294087 < baseStart_6294087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294090 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_6294090 : Nat := 118140960795 + 6294090 * 2 ^ 59
def prefixEnd_6294090 : Nat := 4983230072969 + 3 ^ 40 * 6294090 * 2
def baseEnd_6294090 : Nat := 3231893452657384577629013

theorem tailTrace_6294090 : CollatzResearch.WordTrace tailWord_6294090 prefixEnd_6294090 3231893452657384577629013 := by
  unfold tailWord_6294090
  simp only [CollatzResearch.WordTrace]
  refine ⟨57391080441898587459091931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153042881178396233224245149 57391080441898587459091931)
  ·
    refine ⟨86086620662847881188637897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57391080441898587459091931 86086620662847881188637897)
    ·
      refine ⟨64564965497135910891478423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86086620662847881188637897 64564965497135910891478423)
      ·
        refine ⟨96847448245703866337217635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64564965497135910891478423 96847448245703866337217635)
        ·
          refine ⟨145271172368555799505826453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96847448245703866337217635 145271172368555799505826453)
          ·
            refine ⟨6809586204776053101835615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145271172368555799505826453 6809586204776053101835615)
            ·
              refine ⟨10214379307164079652753423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809586204776053101835615 10214379307164079652753423)
              ·
                refine ⟨15321568960746119479130135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10214379307164079652753423 15321568960746119479130135)
                ·
                  refine ⟨22982353441119179218695203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15321568960746119479130135 22982353441119179218695203)
                  ·
                    refine ⟨34473530161678768828042805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22982353441119179218695203 34473530161678768828042805)
                    ·
                      refine ⟨3231893452657384577629013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34473530161678768828042805 3231893452657384577629013)
                      ·
                        rfl

theorem cell23_6294090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_6294090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294090 prefixEnd_6294090 := by exact prefixLift 6294090
  have htrace : WordTrace (prefixWord ++ tailWord_6294090) baseStart_6294090 baseEnd_6294090 := by
    simpa [prefixWord, tailWord_6294090, baseEnd_6294090] using wordTrace_append hprefix tailTrace_6294090
  have hstable : (prefixWord ++ tailWord_6294090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294090).length < 2 ^ (prefixWord ++ tailWord_6294090).sum := by decide
  have hdescent : baseEnd_6294090 < baseStart_6294090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294093 : List Nat := [1, 6, 1, 1, 2, 12]
def baseStart_6294093 : Nat := 118140960795 + 6294093 * 2 ^ 59
def prefixEnd_6294093 : Nat := 4983230072969 + 3 ^ 40 * 6294093 * 2
def baseEnd_6294093 : Nat := 13299979395470568172393

theorem tailTrace_6294093 : CollatzResearch.WordTrace tailWord_6294093 prefixEnd_6294093 13299979395470568172393 := by
  unfold tailWord_6294093
  simp only [CollatzResearch.WordTrace]
  refine ⟨229564431186583481348726933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153042954124388987565817955 229564431186583481348726933)
  ·
    refine ⟨10760832711871100688221575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229564431186583481348726933 10760832711871100688221575)
    ·
      refine ⟨16141249067806651032332363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10760832711871100688221575 16141249067806651032332363)
      ·
        refine ⟨24211873601709976548498545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16141249067806651032332363 24211873601709976548498545)
        ·
          refine ⟨18158905201282482411373909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24211873601709976548498545 18158905201282482411373909)
          ·
            refine ⟨13299979395470568172393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18158905201282482411373909 13299979395470568172393)
            ·
              rfl

theorem cell23_6294093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 12].length) (baseStart_6294093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294093 prefixEnd_6294093 := by exact prefixLift 6294093
  have htrace : WordTrace (prefixWord ++ tailWord_6294093) baseStart_6294093 baseEnd_6294093 := by
    simpa [prefixWord, tailWord_6294093, baseEnd_6294093] using wordTrace_append hprefix tailTrace_6294093
  have hstable : (prefixWord ++ tailWord_6294093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294093).length < 2 ^ (prefixWord ++ tailWord_6294093).sum := by decide
  have hdescent : baseEnd_6294093 < baseStart_6294093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294096 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_6294096 : Nat := 118140960795 + 6294096 * 2 ^ 59
def prefixEnd_6294096 : Nat := 4983230072969 + 3 ^ 40 * 6294096 * 2
def baseEnd_6294096 : Nat := 3231896533541311554153985

theorem tailTrace_6294096 : CollatzResearch.WordTrace tailWord_6294096 prefixEnd_6294096 3231896533541311554153985 := by
  unfold tailWord_6294096
  simp only [CollatzResearch.WordTrace]
  refine ⟨114782270302786306430543071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153043027070381741907390761 114782270302786306430543071)
  ·
    refine ⟨172173405454179459645814607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114782270302786306430543071 172173405454179459645814607)
    ·
      refine ⟨258260108181269189468721911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172173405454179459645814607 258260108181269189468721911)
      ·
        refine ⟨387390162271903784203082867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258260108181269189468721911 387390162271903784203082867)
        ·
          refine ⟨581085243407855676304624301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387390162271903784203082867 581085243407855676304624301)
          ·
            refine ⟨217906966277945878614234113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581085243407855676304624301 217906966277945878614234113)
            ·
              refine ⟨163430224708459408960675585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217906966277945878614234113 163430224708459408960675585)
              ·
                refine ⟨122572668531344556720506689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163430224708459408960675585 122572668531344556720506689)
                ·
                  refine ⟨91929501398508417540380017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122572668531344556720506689 91929501398508417540380017)
                  ·
                    refine ⟨68947126048881313155285013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91929501398508417540380017 68947126048881313155285013)
                    ·
                      refine ⟨3231896533541311554153985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68947126048881313155285013 3231896533541311554153985)
                      ·
                        rfl

theorem cell23_6294096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_6294096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294096 prefixEnd_6294096 := by exact prefixLift 6294096
  have htrace : WordTrace (prefixWord ++ tailWord_6294096) baseStart_6294096 baseEnd_6294096 := by
    simpa [prefixWord, tailWord_6294096, baseEnd_6294096] using wordTrace_append hprefix tailTrace_6294096
  have hstable : (prefixWord ++ tailWord_6294096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294096).length < 2 ^ (prefixWord ++ tailWord_6294096).sum := by decide
  have hdescent : baseEnd_6294096 < baseStart_6294096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294103 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_6294103 : Nat := 118140960795 + 6294103 * 2 ^ 59
def prefixEnd_6294103 : Nat := 4983230072969 + 3 ^ 40 * 6294103 * 2
def baseEnd_6294103 : Nat := 3231900127905893026766453

theorem tailTrace_6294103 : CollatzResearch.WordTrace tailWord_6294103 prefixEnd_6294103 3231900127905893026766453 := by
  unfold tailWord_6294103
  simp only [CollatzResearch.WordTrace]
  refine ⟨229564795916547253056590963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153043197277698168704393975 229564795916547253056590963)
  ·
    refine ⟨344347193874820879584886445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229564795916547253056590963 344347193874820879584886445)
    ·
      refine ⟨129130197703057829844332417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344347193874820879584886445 129130197703057829844332417)
      ·
        refine ⟨96847648277293372383249313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129130197703057829844332417 96847648277293372383249313)
        ·
          refine ⟨72635736207970029287436985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96847648277293372383249313 72635736207970029287436985)
          ·
            refine ⟨54476802155977521965577739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72635736207970029287436985 54476802155977521965577739)
            ·
              refine ⟨81715203233966282948366609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54476802155977521965577739 81715203233966282948366609)
              ·
                refine ⟨61286402425474712211274957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81715203233966282948366609 61286402425474712211274957)
                ·
                  refine ⟨22982400909553017079228109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61286402425474712211274957 22982400909553017079228109)
                  ·
                    refine ⟨8618400341082381404710541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22982400909553017079228109 8618400341082381404710541)
                    ·
                      refine ⟨3231900127905893026766453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8618400341082381404710541 3231900127905893026766453)
                      ·
                        rfl

theorem cell23_6294103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_6294103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294103 prefixEnd_6294103 := by exact prefixLift 6294103
  have htrace : WordTrace (prefixWord ++ tailWord_6294103) baseStart_6294103 baseEnd_6294103 := by
    simpa [prefixWord, tailWord_6294103, baseEnd_6294103] using wordTrace_append hprefix tailTrace_6294103
  have hstable : (prefixWord ++ tailWord_6294103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294103).length < 2 ^ (prefixWord ++ tailWord_6294103).sum := by decide
  have hdescent : baseEnd_6294103 < baseStart_6294103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294141 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_6294141 : Nat := 118140960795 + 6294141 * 2 ^ 59
def prefixEnd_6294141 : Nat := 4983230072969 + 3 ^ 40 * 6294141 * 2
def baseEnd_6294141 : Nat := 3231919640170763878091279

theorem tailTrace_6294141 : CollatzResearch.WordTrace tailWord_6294141 prefixEnd_6294141 3231919640170763878091279 := by
  unfold tailWord_6294141
  simp only [CollatzResearch.WordTrace]
  refine ⟨229566181890409585546474277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153044121260273057030982851 229566181890409585546474277)
  ·
    refine ⟨43043659104451797289963927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229566181890409585546474277 43043659104451797289963927)
    ·
      refine ⟨64565488656677695934945891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43043659104451797289963927 64565488656677695934945891)
      ·
        refine ⟨96848232985016543902418837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64565488656677695934945891 96848232985016543902418837)
        ·
          refine ⟨4539760921172650495425883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96848232985016543902418837 4539760921172650495425883)
          ·
            refine ⟨6809641381758975743138825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539760921172650495425883 6809641381758975743138825)
            ·
              refine ⟨5107231036319231807354119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6809641381758975743138825 5107231036319231807354119)
              ·
                refine ⟨7660846554478847711031179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107231036319231807354119 7660846554478847711031179)
                ·
                  refine ⟨11491269831718271566546769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660846554478847711031179 11491269831718271566546769)
                  ·
                    refine ⟨8618452373788703674910077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11491269831718271566546769 8618452373788703674910077)
                    ·
                      refine ⟨3231919640170763878091279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8618452373788703674910077 3231919640170763878091279)
                      ·
                        rfl

theorem cell23_6294141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_6294141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294141 prefixEnd_6294141 := by exact prefixLift 6294141
  have htrace : WordTrace (prefixWord ++ tailWord_6294141) baseStart_6294141 baseEnd_6294141 := by
    simpa [prefixWord, tailWord_6294141, baseEnd_6294141] using wordTrace_append hprefix tailTrace_6294141
  have hstable : (prefixWord ++ tailWord_6294141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294141).length < 2 ^ (prefixWord ++ tailWord_6294141).sum := by decide
  have hdescent : baseEnd_6294141 < baseStart_6294141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294263 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_6294263 : Nat := 118140960795 + 6294263 * 2 ^ 59
def prefixEnd_6294263 : Nat := 4983230072969 + 3 ^ 40 * 6294263 * 2
def baseEnd_6294263 : Nat := 3231982284810612400765717

theorem tailTrace_6294263 : CollatzResearch.WordTrace tailWord_6294263 prefixEnd_6294263 3231982284810612400765717 := by
  unfold tailWord_6294263
  simp only [CollatzResearch.WordTrace]
  refine ⟨229570631595967600382415443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153047087730645066921610295 229570631595967600382415443)
  ·
    refine ⟨344355947393951400573623165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229570631595967600382415443 344355947393951400573623165)
    ·
      refine ⟨129133480272731775215108687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344355947393951400573623165 129133480272731775215108687)
      ·
        refine ⟨193700220409097662822663031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129133480272731775215108687 193700220409097662822663031)
        ·
          refine ⟨290550330613646494233994547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193700220409097662822663031 290550330613646494233994547)
          ·
            refine ⟨435825495920469741350991821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290550330613646494233994547 435825495920469741350991821)
            ·
              refine ⟨163434560970176153006621933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435825495920469741350991821 163434560970176153006621933)
              ·
                refine ⟨61287960363816057377483225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163434560970176153006621933 61287960363816057377483225)
                ·
                  refine ⟨45965970272862043033112419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61287960363816057377483225 45965970272862043033112419)
                  ·
                    refine ⟨68948955409293064549668629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45965970272862043033112419 68948955409293064549668629)
                    ·
                      refine ⟨3231982284810612400765717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68948955409293064549668629 3231982284810612400765717)
                      ·
                        rfl

theorem cell23_6294263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_6294263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294263 prefixEnd_6294263 := by exact prefixLift 6294263
  have htrace : WordTrace (prefixWord ++ tailWord_6294263) baseStart_6294263 baseEnd_6294263 := by
    simpa [prefixWord, tailWord_6294263, baseEnd_6294263] using wordTrace_append hprefix tailTrace_6294263
  have hstable : (prefixWord ++ tailWord_6294263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294263).length < 2 ^ (prefixWord ++ tailWord_6294263).sum := by decide
  have hdescent : baseEnd_6294263 < baseStart_6294263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294301 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6294301 : Nat := 118140960795 + 6294301 * 2 ^ 59
def prefixEnd_6294301 : Nat := 4983230072969 + 3 ^ 40 * 6294301 * 2
def baseEnd_6294301 : Nat := 3232001797075483252090543

theorem tailTrace_6294301 : CollatzResearch.WordTrace tailWord_6294301 prefixEnd_6294301 3232001797075483252090543 := by
  unfold tailWord_6294301
  simp only [CollatzResearch.WordTrace]
  refine ⟨229572017569829932872298757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153048011713219955248199171 229572017569829932872298757)
  ·
    refine ⟨43044753294343112413556017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229572017569829932872298757 43044753294343112413556017)
    ·
      refine ⟨32283564970757334310167013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43044753294343112413556017 32283564970757334310167013)
      ·
        refine ⟨6053168432017000183156315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32283564970757334310167013 6053168432017000183156315)
        ·
          refine ⟨9079752648025500274734473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053168432017000183156315 9079752648025500274734473)
          ·
            refine ⟨6809814486019125206050855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9079752648025500274734473 6809814486019125206050855)
            ·
              refine ⟨10214721729028687809076283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809814486019125206050855 10214721729028687809076283)
              ·
                refine ⟨15322082593543031713614425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10214721729028687809076283 15322082593543031713614425)
                ·
                  refine ⟨11491561945157273785210819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15322082593543031713614425 11491561945157273785210819)
                  ·
                    refine ⟨17237342917735910677816229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11491561945157273785210819 17237342917735910677816229)
                    ·
                      refine ⟨3232001797075483252090543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17237342917735910677816229 3232001797075483252090543)
                      ·
                        rfl

theorem cell23_6294301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6294301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294301 prefixEnd_6294301 := by exact prefixLift 6294301
  have htrace : WordTrace (prefixWord ++ tailWord_6294301) baseStart_6294301 baseEnd_6294301 := by
    simpa [prefixWord, tailWord_6294301, baseEnd_6294301] using wordTrace_append hprefix tailTrace_6294301
  have hstable : (prefixWord ++ tailWord_6294301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294301).length < 2 ^ (prefixWord ++ tailWord_6294301).sum := by decide
  have hdescent : baseEnd_6294301 < baseStart_6294301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294304 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6294304 : Nat := 118140960795 + 6294304 * 2 ^ 59
def prefixEnd_6294304 : Nat := 4983230072969 + 3 ^ 40 * 6294304 * 2
def baseEnd_6294304 : Nat := 3232003337517446740353029

theorem tailTrace_6294304 : CollatzResearch.WordTrace tailWord_6294304 prefixEnd_6294304 3232003337517446740353029 := by
  unfold tailWord_6294304
  simp only [CollatzResearch.WordTrace]
  refine ⟨114786063494409532192328983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153048084659212709589771977 114786063494409532192328983)
  ·
    refine ⟨172179095241614298288493475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114786063494409532192328983 172179095241614298288493475)
    ·
      refine ⟨258268642862421447432740213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172179095241614298288493475 258268642862421447432740213)
      ·
        refine ⟨24212685268352010696819395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258268642862421447432740213 24212685268352010696819395)
        ·
          refine ⟨36319027902528016045229093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24212685268352010696819395 36319027902528016045229093)
          ·
            refine ⟨6809817731724003008480455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36319027902528016045229093 6809817731724003008480455)
            ·
              refine ⟨10214726597586004512720683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809817731724003008480455 10214726597586004512720683)
              ·
                refine ⟨15322089896379006769081025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10214726597586004512720683 15322089896379006769081025)
                ·
                  refine ⟨11491567422284255076810769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15322089896379006769081025 11491567422284255076810769)
                  ·
                    refine ⟨8618675566713191307608077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11491567422284255076810769 8618675566713191307608077)
                    ·
                      refine ⟨3232003337517446740353029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8618675566713191307608077 3232003337517446740353029)
                      ·
                        rfl

theorem cell23_6294304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6294304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294304 prefixEnd_6294304 := by exact prefixLift 6294304
  have htrace : WordTrace (prefixWord ++ tailWord_6294304) baseStart_6294304 baseEnd_6294304 := by
    simpa [prefixWord, tailWord_6294304, baseEnd_6294304] using wordTrace_append hprefix tailTrace_6294304
  have hstable : (prefixWord ++ tailWord_6294304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294304).length < 2 ^ (prefixWord ++ tailWord_6294304).sum := by decide
  have hdescent : baseEnd_6294304 < baseStart_6294304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294313 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_6294313 : Nat := 118140960795 + 6294313 * 2 ^ 59
def prefixEnd_6294313 : Nat := 4983230072969 + 3 ^ 40 * 6294313 * 2
def baseEnd_6294313 : Nat := 3232007958843337205140487

theorem tailTrace_6294313 : CollatzResearch.WordTrace tailWord_6294313 prefixEnd_6294313 3232007958843337205140487 := by
  unfold tailWord_6294313
  simp only [CollatzResearch.WordTrace]
  refine ⟨229572455245786458921735593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153048303497190972614490395 229572455245786458921735593)
  ·
    refine ⟨172179341434339844191301695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229572455245786458921735593 172179341434339844191301695)
    ·
      refine ⟨258269012151509766286952543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172179341434339844191301695 258269012151509766286952543)
      ·
        refine ⟨387403518227264649430428815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258269012151509766286952543 387403518227264649430428815)
        ·
          refine ⟨581105277340896974145643223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387403518227264649430428815 581105277340896974145643223)
          ·
            refine ⟨871657916011345461218464835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581105277340896974145643223 871657916011345461218464835)
            ·
              refine ⟨1307486874017018191827697253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871657916011345461218464835 1307486874017018191827697253)
              ·
                refine ⟨245153788878190910967693235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1307486874017018191827697253 245153788878190910967693235)
                ·
                  refine ⟨367730683317286366451539853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245153788878190910967693235 367730683317286366451539853)
                  ·
                    refine ⟨137899006243982387419327445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 367730683317286366451539853 137899006243982387419327445)
                    ·
                      refine ⟨3232007958843337205140487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137899006243982387419327445 3232007958843337205140487)
                      ·
                        rfl

theorem cell23_6294313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_6294313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294313 prefixEnd_6294313 := by exact prefixLift 6294313
  have htrace : WordTrace (prefixWord ++ tailWord_6294313) baseStart_6294313 baseEnd_6294313 := by
    simpa [prefixWord, tailWord_6294313, baseEnd_6294313] using wordTrace_append hprefix tailTrace_6294313
  have hstable : (prefixWord ++ tailWord_6294313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294313).length < 2 ^ (prefixWord ++ tailWord_6294313).sum := by decide
  have hdescent : baseEnd_6294313 < baseStart_6294313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294327 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_6294327 : Nat := 118140960795 + 6294327 * 2 ^ 59
def prefixEnd_6294327 : Nat := 4983230072969 + 3 ^ 40 * 6294327 * 2
def baseEnd_6294327 : Nat := 3232015147572500150365423

theorem tailTrace_6294327 : CollatzResearch.WordTrace tailWord_6294327 prefixEnd_6294327 3232015147572500150365423 := by
  unfold tailWord_6294327
  simp only [CollatzResearch.WordTrace]
  refine ⟨229572965867735739312745235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153048643911823826208496823 229572965867735739312745235)
  ·
    refine ⟨344359448801603608969117853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229572965867735739312745235 344359448801603608969117853)
    ·
      refine ⟨129134793300601353363419195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344359448801603608969117853 129134793300601353363419195)
      ·
        refine ⟨193702189950902030045128793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129134793300601353363419195 193702189950902030045128793)
        ·
          refine ⟨145276642463176522533846595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193702189950902030045128793 145276642463176522533846595)
          ·
            refine ⟨217914963694764783800769893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145276642463176522533846595 217914963694764783800769893)
            ·
              refine ⟨40859055692768396962644355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217914963694764783800769893 40859055692768396962644355)
              ·
                refine ⟨61288583539152595443966533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40859055692768396962644355 61288583539152595443966533)
                ·
                  refine ⟨11491609413591111645743725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61288583539152595443966533 11491609413591111645743725)
                  ·
                    refine ⟨4309353530096666867153897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11491609413591111645743725 4309353530096666867153897)
                    ·
                      refine ⟨3232015147572500150365423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309353530096666867153897 3232015147572500150365423)
                      ·
                        rfl

theorem cell23_6294327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_6294327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294327 prefixEnd_6294327 := by exact prefixLift 6294327
  have htrace : WordTrace (prefixWord ++ tailWord_6294327) baseStart_6294327 baseEnd_6294327 := by
    simpa [prefixWord, tailWord_6294327, baseEnd_6294327] using wordTrace_append hprefix tailTrace_6294327
  have hstable : (prefixWord ++ tailWord_6294327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294327).length < 2 ^ (prefixWord ++ tailWord_6294327).sum := by decide
  have hdescent : baseEnd_6294327 < baseStart_6294327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294357 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6294357 : Nat := 118140960795 + 6294357 * 2 ^ 59
def prefixEnd_6294357 : Nat := 4983230072969 + 3 ^ 40 * 6294357 * 2
def baseEnd_6294357 : Nat := 3232030551992135032990285

theorem tailTrace_6294357 : CollatzResearch.WordTrace tailWord_6294357 prefixEnd_6294357 3232030551992135032990285 := by
  unfold tailWord_6294357
  simp only [CollatzResearch.WordTrace]
  refine ⟨229574060057627054436337325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153049373371751369624224883 229574060057627054436337325)
  ·
    refine ⟨86090272521610145413626497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229574060057627054436337325 86090272521610145413626497)
    ·
      refine ⟨64567704391207609060219873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86090272521610145413626497 64567704391207609060219873)
      ·
        refine ⟨48425778293405706795164905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64567704391207609060219873 48425778293405706795164905)
        ·
          refine ⟨36319333720054280096373679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48425778293405706795164905 36319333720054280096373679)
          ·
            refine ⟨54479000580081420144560519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36319333720054280096373679 54479000580081420144560519)
            ·
              refine ⟨81718500870122130216840779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54479000580081420144560519 81718500870122130216840779)
              ·
                refine ⟨122577751305183195325261169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81718500870122130216840779 122577751305183195325261169)
                ·
                  refine ⟨91933313478887396493945877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122577751305183195325261169 91933313478887396493945877)
                  ·
                    refine ⟨4309374069322846710653713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91933313478887396493945877 4309374069322846710653713)
                    ·
                      refine ⟨3232030551992135032990285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309374069322846710653713 3232030551992135032990285)
                      ·
                        rfl

theorem cell23_6294357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6294357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294357 prefixEnd_6294357 := by exact prefixLift 6294357
  have htrace : WordTrace (prefixWord ++ tailWord_6294357) baseStart_6294357 baseEnd_6294357 := by
    simpa [prefixWord, tailWord_6294357, baseEnd_6294357] using wordTrace_append hprefix tailTrace_6294357
  have hstable : (prefixWord ++ tailWord_6294357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294357).length < 2 ^ (prefixWord ++ tailWord_6294357).sum := by decide
  have hdescent : baseEnd_6294357 < baseStart_6294357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294360 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_6294360 : Nat := 118140960795 + 6294360 * 2 ^ 59
def prefixEnd_6294360 : Nat := 4983230072969 + 3 ^ 40 * 6294360 * 2
def baseEnd_6294360 : Nat := 3232032092434098521252771

theorem tailTrace_6294360 : CollatzResearch.WordTrace tailWord_6294360 prefixEnd_6294360 3232032092434098521252771 := by
  unfold tailWord_6294360
  simp only [CollatzResearch.WordTrace]
  refine ⟨114787084738308092974348267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153049446317744123965797689 114787084738308092974348267)
  ·
    refine ⟨172180627107462139461522401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114787084738308092974348267 172180627107462139461522401)
    ·
      refine ⟨129135470330596604596141801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172180627107462139461522401 129135470330596604596141801)
      ·
        refine ⟨96851602747947453447106351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129135470330596604596141801 96851602747947453447106351)
        ·
          refine ⟨145277404121921180170659527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96851602747947453447106351 145277404121921180170659527)
          ·
            refine ⟨217916106182881770255989291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145277404121921180170659527 217916106182881770255989291)
            ·
              refine ⟨326874159274322655383983937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217916106182881770255989291 326874159274322655383983937)
              ·
                refine ⟨245155619455741991537987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326874159274322655383983937 245155619455741991537987953)
                ·
                  refine ⟨183866714591806493653490965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245155619455741991537987953 183866714591806493653490965)
                  ·
                    refine ⟨8618752246490929390007389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 183866714591806493653490965 8618752246490929390007389)
                    ·
                      refine ⟨3232032092434098521252771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8618752246490929390007389 3232032092434098521252771)
                      ·
                        rfl

theorem cell23_6294360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_6294360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294360 prefixEnd_6294360 := by exact prefixLift 6294360
  have htrace : WordTrace (prefixWord ++ tailWord_6294360) baseStart_6294360 baseEnd_6294360 := by
    simpa [prefixWord, tailWord_6294360, baseEnd_6294360] using wordTrace_append hprefix tailTrace_6294360
  have hstable : (prefixWord ++ tailWord_6294360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294360).length < 2 ^ (prefixWord ++ tailWord_6294360).sum := by decide
  have hdescent : baseEnd_6294360 < baseStart_6294360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294391 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 1, 2, 2]
def baseStart_6294391 : Nat := 118140960795 + 6294391 * 2 ^ 59
def prefixEnd_6294391 : Nat := 4983230072969 + 3 ^ 40 * 6294391 * 2
def baseEnd_6294391 : Nat := 3232048010334387899965129

theorem tailTrace_6294391 : CollatzResearch.WordTrace tailWord_6294391 prefixEnd_6294391 3232048010334387899965129 := by
  unfold tailWord_6294391
  simp only [CollatzResearch.WordTrace]
  refine ⟨229575300139503878243075027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153050200093002585495383351 229575300139503878243075027)
  ·
    refine ⟨344362950209255817364612541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229575300139503878243075027 344362950209255817364612541)
    ·
      refine ⟨129136106328470931511729703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344362950209255817364612541 129136106328470931511729703)
      ·
        refine ⟨193704159492706397267594555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129136106328470931511729703 193704159492706397267594555)
        ·
          refine ⟨290556239239059595901391833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193704159492706397267594555 290556239239059595901391833)
          ·
            refine ⟨217917179429294696926043875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290556239239059595901391833 217917179429294696926043875)
            ·
              refine ⟨326875769143942045389065813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217917179429294696926043875 326875769143942045389065813)
              ·
                refine ⟨3830575419655570844403115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 326875769143942045389065813 3830575419655570844403115)
                ·
                  refine ⟨5745863129483356266604673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830575419655570844403115 5745863129483356266604673)
                  ·
                    refine ⟨4309397347112517199953505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745863129483356266604673 4309397347112517199953505)
                    ·
                      refine ⟨3232048010334387899965129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309397347112517199953505 3232048010334387899965129)
                      ·
                        rfl

theorem cell23_6294391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_6294391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294391 prefixEnd_6294391 := by exact prefixLift 6294391
  have htrace : WordTrace (prefixWord ++ tailWord_6294391) baseStart_6294391 baseEnd_6294391 := by
    simpa [prefixWord, tailWord_6294391, baseEnd_6294391] using wordTrace_append hprefix tailTrace_6294391
  have hstable : (prefixWord ++ tailWord_6294391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294391).length < 2 ^ (prefixWord ++ tailWord_6294391).sum := by decide
  have hdescent : baseEnd_6294391 < baseStart_6294391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294428 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6294428 : Nat := 118140960795 + 6294428 * 2 ^ 59
def prefixEnd_6294428 : Nat := 4983230072969 + 3 ^ 40 * 6294428 * 2
def baseEnd_6294428 : Nat := 3232067009118604255202459

theorem tailTrace_6294428 : CollatzResearch.WordTrace tailWord_6294428 prefixEnd_6294428 3232067009118604255202459 := by
  unfold tailWord_6294428
  simp only [CollatzResearch.WordTrace]
  refine ⟨114788324820184916781085969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153051099760246555708114625 114788324820184916781085969)
  ·
    refine ⟨86091243615138687585814477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114788324820184916781085969 86091243615138687585814477)
    ·
      refine ⟨32284216355677007844680429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86091243615138687585814477 32284216355677007844680429)
      ·
        refine ⟨12106581133378877941755161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32284216355677007844680429 12106581133378877941755161)
        ·
          refine ⟨9079935850034158456316371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12106581133378877941755161 9079935850034158456316371)
          ·
            refine ⟨13619903775051237684474557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079935850034158456316371 13619903775051237684474557)
            ·
              refine ⟨5107463915644214131677959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13619903775051237684474557 5107463915644214131677959)
              ·
                refine ⟨7661195873466321197516939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107463915644214131677959 7661195873466321197516939)
                ·
                  refine ⟨11491793810199481796275409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7661195873466321197516939 11491793810199481796275409)
                  ·
                    refine ⟨8618845357649611347206557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11491793810199481796275409 8618845357649611347206557)
                    ·
                      refine ⟨3232067009118604255202459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8618845357649611347206557 3232067009118604255202459)
                      ·
                        rfl

theorem cell23_6294428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6294428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294428 prefixEnd_6294428 := by exact prefixLift 6294428
  have htrace : WordTrace (prefixWord ++ tailWord_6294428) baseStart_6294428 baseEnd_6294428 := by
    simpa [prefixWord, tailWord_6294428, baseEnd_6294428] using wordTrace_append hprefix tailTrace_6294428
  have hstable : (prefixWord ++ tailWord_6294428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294428).length < 2 ^ (prefixWord ++ tailWord_6294428).sum := by decide
  have hdescent : baseEnd_6294428 < baseStart_6294428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294457 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_6294457 : Nat := 118140960795 + 6294457 * 2 ^ 59
def prefixEnd_6294457 : Nat := 4983230072969 + 3 ^ 40 * 6294457 * 2
def baseEnd_6294457 : Nat := 1077360633352528213913275

theorem tailTrace_6294457 : CollatzResearch.WordTrace tailWord_6294457 prefixEnd_6294457 1077360633352528213913275 := by
  unfold tailWord_6294457
  simp only [CollatzResearch.WordTrace]
  refine ⟨229577707357264771514977625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153051804904843181009985083 229577707357264771514977625)
  ·
    refine ⟨172183280517948578636233219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229577707357264771514977625 172183280517948578636233219)
    ·
      refine ⟨258274920776922867954349829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172183280517948578636233219 258274920776922867954349829)
      ·
        refine ⟨48426547645673037741440593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258274920776922867954349829 48426547645673037741440593)
        ·
          refine ⟨36319910734254778306080445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48426547645673037741440593 36319910734254778306080445)
          ·
            refine ⟨13619966525345541864780167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36319910734254778306080445 13619966525345541864780167)
            ·
              refine ⟨20429949788018312797170251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13619966525345541864780167 20429949788018312797170251)
              ·
                refine ⟨30644924682027469195755377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20429949788018312797170251 30644924682027469195755377)
                ·
                  refine ⟨22983693511520601896816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30644924682027469195755377 22983693511520601896816533)
                  ·
                    refine ⟨1077360633352528213913275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22983693511520601896816533 1077360633352528213913275)
                    ·
                      rfl

theorem cell23_6294457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_6294457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294457 prefixEnd_6294457 := by exact prefixLift 6294457
  have htrace : WordTrace (prefixWord ++ tailWord_6294457) baseStart_6294457 baseEnd_6294457 := by
    simpa [prefixWord, tailWord_6294457, baseEnd_6294457] using wordTrace_append hprefix tailTrace_6294457
  have hstable : (prefixWord ++ tailWord_6294457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294457).length < 2 ^ (prefixWord ++ tailWord_6294457).sum := by decide
  have hdescent : baseEnd_6294457 < baseStart_6294457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294464 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2]
def baseStart_6294464 : Nat := 118140960795 + 6294464 * 2 ^ 59
def prefixEnd_6294464 : Nat := 4983230072969 + 3 ^ 40 * 6294464 * 2
def baseEnd_6294464 : Nat := 3232085494422166114352293

theorem tailTrace_6294464 : CollatzResearch.WordTrace tailWord_6294464 prefixEnd_6294464 3232085494422166114352293 := by
  unfold tailWord_6294464
  simp only [CollatzResearch.WordTrace]
  refine ⟨114788981334119705855241223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153051975112159607806988297 114788981334119705855241223)
  ·
    refine ⟨172183472001179558782861835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114788981334119705855241223 172183472001179558782861835)
    ·
      refine ⟨258275208001769338174292753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172183472001179558782861835 258275208001769338174292753)
      ·
        refine ⟨193706406001327003630719565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258275208001769338174292753 193706406001327003630719565)
        ·
          refine ⟨72639902250497626361519837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193706406001327003630719565 72639902250497626361519837)
          ·
            refine ⟨27239963343936609885569939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72639902250497626361519837 27239963343936609885569939)
            ·
              refine ⟨40859945015904914828354909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27239963343936609885569939 40859945015904914828354909)
              ·
                refine ⟨15322479380964343060633091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40859945015904914828354909 15322479380964343060633091)
                ·
                  refine ⟨22983719071446514590949637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15322479380964343060633091 22983719071446514590949637)
                  ·
                    refine ⟨4309447325896221485803057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22983719071446514590949637 4309447325896221485803057)
                    ·
                      refine ⟨3232085494422166114352293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309447325896221485803057 3232085494422166114352293)
                      ·
                        rfl

theorem cell23_6294464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_6294464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294464 prefixEnd_6294464 := by exact prefixLift 6294464
  have htrace : WordTrace (prefixWord ++ tailWord_6294464) baseStart_6294464 baseEnd_6294464 := by
    simpa [prefixWord, tailWord_6294464, baseEnd_6294464] using wordTrace_append hprefix tailTrace_6294464
  have hstable : (prefixWord ++ tailWord_6294464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294464).length < 2 ^ (prefixWord ++ tailWord_6294464).sum := by decide
  have hdescent : baseEnd_6294464 < baseStart_6294464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294480 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_6294480 : Nat := 118140960795 + 6294480 * 2 ^ 59
def prefixEnd_6294480 : Nat := 4983230072969 + 3 ^ 40 * 6294480 * 2
def baseEnd_6294480 : Nat := 3232093710112638051752219

theorem tailTrace_6294480 : CollatzResearch.WordTrace tailWord_6294480 prefixEnd_6294480 3232093710112638051752219 := by
  unfold tailWord_6294480
  simp only [CollatzResearch.WordTrace]
  refine ⟨114789273118090723221532447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153052364157454297628709929 114789273118090723221532447)
  ·
    refine ⟨172183909677136084832298671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114789273118090723221532447 172183909677136084832298671)
    ·
      refine ⟨258275864515704127248448007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172183909677136084832298671 258275864515704127248448007)
      ·
        refine ⟨387413796773556190872672011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258275864515704127248448007 387413796773556190872672011)
        ·
          refine ⟨581120695160334286309008017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387413796773556190872672011 581120695160334286309008017)
          ·
            refine ⟨435840521370250714731756013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581120695160334286309008017 435840521370250714731756013)
            ·
              refine ⟨163440195513844018024408505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435840521370250714731756013 163440195513844018024408505)
              ·
                refine ⟨122580146635383013518306379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163440195513844018024408505 122580146635383013518306379)
                ·
                  refine ⟨183870219953074520277459569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122580146635383013518306379 183870219953074520277459569)
                  ·
                    refine ⟨137902664964805890208094677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183870219953074520277459569 137902664964805890208094677)
                    ·
                      refine ⟨3232093710112638051752219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137902664964805890208094677 3232093710112638051752219)
                      ·
                        rfl

theorem cell23_6294480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_6294480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294480 prefixEnd_6294480 := by exact prefixLift 6294480
  have htrace : WordTrace (prefixWord ++ tailWord_6294480) baseStart_6294480 baseEnd_6294480 := by
    simpa [prefixWord, tailWord_6294480, baseEnd_6294480] using wordTrace_append hprefix tailTrace_6294480
  have hstable : (prefixWord ++ tailWord_6294480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294480).length < 2 ^ (prefixWord ++ tailWord_6294480).sum := by decide
  have hdescent : baseEnd_6294480 < baseStart_6294480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294485 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6294485 : Nat := 118140960795 + 6294485 * 2 ^ 59
def prefixEnd_6294485 : Nat := 4983230072969 + 3 ^ 40 * 6294485 * 2
def baseEnd_6294485 : Nat := 3232096277515910532189697

theorem tailTrace_6294485 : CollatzResearch.WordTrace tailWord_6294485 prefixEnd_6294485 3232096277515910532189697 := by
  unfold tailWord_6294485
  simp only [CollatzResearch.WordTrace]
  refine ⟨229578728601163332296996909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153052485734108888197997939 229578728601163332296996909)
  ·
    refine ⟨86092023225436249611373841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229578728601163332296996909 86092023225436249611373841)
    ·
      refine ⟨64569017419077187208530381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86092023225436249611373841 64569017419077187208530381)
      ·
        refine ⟨24213381532153945203198893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64569017419077187208530381 24213381532153945203198893)
        ·
          refine ⟨9080018074557729451199585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24213381532153945203198893 9080018074557729451199585)
          ·
            refine ⟨6810013555918297088399689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080018074557729451199585 6810013555918297088399689)
            ·
              refine ⟨5107510166938722816299767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810013555918297088399689 5107510166938722816299767)
              ·
                refine ⟨7661265250408084224449651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107510166938722816299767 7661265250408084224449651)
                ·
                  refine ⟨11491897875612126336674477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7661265250408084224449651 11491897875612126336674477)
                  ·
                    refine ⟨4309461703354547376252929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11491897875612126336674477 4309461703354547376252929)
                    ·
                      refine ⟨3232096277515910532189697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309461703354547376252929 3232096277515910532189697)
                      ·
                        rfl

theorem cell23_6294485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6294485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294485 prefixEnd_6294485 := by exact prefixLift 6294485
  have htrace : WordTrace (prefixWord ++ tailWord_6294485) baseStart_6294485 baseEnd_6294485 := by
    simpa [prefixWord, tailWord_6294485, baseEnd_6294485] using wordTrace_append hprefix tailTrace_6294485
  have hstable : (prefixWord ++ tailWord_6294485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294485).length < 2 ^ (prefixWord ++ tailWord_6294485).sum := by decide
  have hdescent : baseEnd_6294485 < baseStart_6294485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294504 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 5]
def baseStart_6294504 : Nat := 118140960795 + 6294504 * 2 ^ 59
def prefixEnd_6294504 : Nat := 4983230072969 + 3 ^ 40 * 6294504 * 2
def baseEnd_6294504 : Nat := 359122892627593995316901

theorem tailTrace_6294504 : CollatzResearch.WordTrace tailWord_6294504 prefixEnd_6294504 359122892627593995316901 := by
  unfold tailWord_6294504
  simp only [CollatzResearch.WordTrace]
  refine ⟨114789710794047249270969283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153052947725396332361292377 114789710794047249270969283)
  ·
    refine ⟨172184566191070873906453925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114789710794047249270969283 172184566191070873906453925)
    ·
      refine ⟨32284606160825788857460111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172184566191070873906453925 32284606160825788857460111)
      ·
        refine ⟨48426909241238683286190167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32284606160825788857460111 48426909241238683286190167)
        ·
          refine ⟨72640363861858024929285251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48426909241238683286190167 72640363861858024929285251)
          ·
            refine ⟨108960545792787037393927877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72640363861858024929285251 108960545792787037393927877)
            ·
              refine ⟨20430102336147569511361477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108960545792787037393927877 20430102336147569511361477)
              ·
                refine ⟨3830644188027669283380277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20430102336147569511361477 3830644188027669283380277)
                ·
                  refine ⟨359122892627593995316901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3830644188027669283380277 359122892627593995316901)
                  ·
                    rfl

theorem cell23_6294504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 5].length) (baseStart_6294504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294504 prefixEnd_6294504 := by exact prefixLift 6294504
  have htrace : WordTrace (prefixWord ++ tailWord_6294504) baseStart_6294504 baseEnd_6294504 := by
    simpa [prefixWord, tailWord_6294504, baseEnd_6294504] using wordTrace_append hprefix tailTrace_6294504
  have hstable : (prefixWord ++ tailWord_6294504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294504).length < 2 ^ (prefixWord ++ tailWord_6294504).sum := by decide
  have hdescent : baseEnd_6294504 < baseStart_6294504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294537 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_6294537 : Nat := 118140960795 + 6294537 * 2 ^ 59
def prefixEnd_6294537 : Nat := 4983230072969 + 3 ^ 40 * 6294537 * 2
def baseEnd_6294537 : Nat := 3232122978509944328739457

theorem tailTrace_6294537 : CollatzResearch.WordTrace tailWord_6294537 prefixEnd_6294537 3232122978509944328739457 := by
  unfold tailWord_6294537
  simp only [CollatzResearch.WordTrace]
  refine ⟨229580625196974945177889865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153053750131316630118593243 229580625196974945177889865)
  ·
    refine ⟨172185468897731208883417399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229580625196974945177889865 172185468897731208883417399)
    ·
      refine ⟨258278203346596813325126099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172185468897731208883417399 258278203346596813325126099)
      ·
        refine ⟨387417305019895219987689149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258278203346596813325126099 387417305019895219987689149)
        ·
          refine ⟨145281489382460707495383431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387417305019895219987689149 145281489382460707495383431)
          ·
            refine ⟨217922234073691061243075147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145281489382460707495383431 217922234073691061243075147)
            ·
              refine ⟨326883351110536591864612721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217922234073691061243075147 326883351110536591864612721)
              ·
                refine ⟨245162513332902443898459541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326883351110536591864612721 245162513332902443898459541)
                ·
                  refine ⟨11491992812479802057740291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 245162513332902443898459541 11491992812479802057740291)
                  ·
                    refine ⟨17237989218719703086610437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11491992812479802057740291 17237989218719703086610437)
                    ·
                      refine ⟨3232122978509944328739457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17237989218719703086610437 3232122978509944328739457)
                      ·
                        rfl

theorem cell23_6294537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_6294537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294537 prefixEnd_6294537 := by exact prefixLift 6294537
  have htrace : WordTrace (prefixWord ++ tailWord_6294537) baseStart_6294537 baseEnd_6294537 := by
    simpa [prefixWord, tailWord_6294537, baseEnd_6294537] using wordTrace_append hprefix tailTrace_6294537
  have hstable : (prefixWord ++ tailWord_6294537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294537).length < 2 ^ (prefixWord ++ tailWord_6294537).sum := by decide
  have hdescent : baseEnd_6294537 < baseStart_6294537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294554 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_6294554 : Nat := 118140960795 + 6294554 * 2 ^ 59
def prefixEnd_6294554 : Nat := 4983230072969 + 3 ^ 40 * 6294554 * 2
def baseEnd_6294554 : Nat := 3232131707681070762226879

theorem tailTrace_6294554 : CollatzResearch.WordTrace tailWord_6294554 prefixEnd_6294554 3232131707681070762226879 := by
  unfold tailWord_6294554
  simp only [CollatzResearch.WordTrace]
  refine ⟨57395311309478339270314679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153054163491942238054172477 57395311309478339270314679)
  ·
    refine ⟨86092966964217508905472019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57395311309478339270314679 86092966964217508905472019)
    ·
      refine ⟨129139450446326263358208029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86092966964217508905472019 129139450446326263358208029)
      ·
        refine ⟨48427293917372348759328011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129139450446326263358208029 48427293917372348759328011)
        ·
          refine ⟨72640940876058523138992017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48427293917372348759328011 72640940876058523138992017)
          ·
            refine ⟨54480705657043892354244013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72640940876058523138992017 54480705657043892354244013)
            ·
              refine ⟨20430264621391459632841505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54480705657043892354244013 20430264621391459632841505)
              ·
                refine ⟨15322698466043594724631129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20430264621391459632841505 15322698466043594724631129)
                ·
                  refine ⟨11492023849532696043473347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15322698466043594724631129 11492023849532696043473347)
                  ·
                    refine ⟨17238035774299044065210021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11492023849532696043473347 17238035774299044065210021)
                    ·
                      refine ⟨3232131707681070762226879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17238035774299044065210021 3232131707681070762226879)
                      ·
                        rfl

theorem cell23_6294554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_6294554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294554 prefixEnd_6294554 := by exact prefixLift 6294554
  have htrace : WordTrace (prefixWord ++ tailWord_6294554) baseStart_6294554 baseEnd_6294554 := by
    simpa [prefixWord, tailWord_6294554, baseEnd_6294554] using wordTrace_append hprefix tailTrace_6294554
  have hstable : (prefixWord ++ tailWord_6294554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294554).length < 2 ^ (prefixWord ++ tailWord_6294554).sum := by decide
  have hdescent : baseEnd_6294554 < baseStart_6294554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294607 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 7, 5]
def baseStart_6294607 : Nat := 118140960795 + 6294607 * 2 ^ 59
def prefixEnd_6294607 : Nat := 4983230072969 + 3 ^ 40 * 6294607 * 2
def baseEnd_6294607 : Nat := 1077386307385253018288045

theorem tailTrace_6294607 : CollatzResearch.WordTrace tailWord_6294607 prefixEnd_6294607 1077386307385253018288045 := by
  unfold tailWord_6294607
  simp only [CollatzResearch.WordTrace]
  refine ⟨229583178306721347132938075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153055452204480898088625383 229583178306721347132938075)
  ·
    refine ⟨344374767460082020699407113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229583178306721347132938075 344374767460082020699407113)
    ·
      refine ⟨258281075595061515524555335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344374767460082020699407113 258281075595061515524555335)
      ·
        refine ⟨387421613392592273286833003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258281075595061515524555335 387421613392592273286833003)
        ·
          refine ⟨581132420088888409930249505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387421613392592273286833003 581132420088888409930249505)
          ·
            refine ⟨435849315066666307447687129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581132420088888409930249505 435849315066666307447687129)
            ·
              refine ⟨326886986299999730585765347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435849315066666307447687129 326886986299999730585765347)
              ·
                refine ⟨490330479449999595878648021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326886986299999730585765347 490330479449999595878648021)
                ·
                  refine ⟨11492120612109365528405813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 490330479449999595878648021 11492120612109365528405813)
                  ·
                    refine ⟨1077386307385253018288045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11492120612109365528405813 1077386307385253018288045)
                    ·
                      rfl

theorem cell23_6294607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_6294607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294607 prefixEnd_6294607 := by exact prefixLift 6294607
  have htrace : WordTrace (prefixWord ++ tailWord_6294607) baseStart_6294607 baseEnd_6294607 := by
    simpa [prefixWord, tailWord_6294607, baseEnd_6294607] using wordTrace_append hprefix tailTrace_6294607
  have hstable : (prefixWord ++ tailWord_6294607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294607).length < 2 ^ (prefixWord ++ tailWord_6294607).sum := by decide
  have hdescent : baseEnd_6294607 < baseStart_6294607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294638 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_6294638 : Nat := 118140960795 + 6294638 * 2 ^ 59
def prefixEnd_6294638 : Nat := 4983230072969 + 3 ^ 40 * 6294638 * 2
def baseEnd_6294638 : Nat := 3232174840056048433576493

theorem tailTrace_6294638 : CollatzResearch.WordTrace tailWord_6294638 prefixEnd_6294638 3232174840056048433576493 := by
  unfold tailWord_6294638
  simp only [CollatzResearch.WordTrace]
  refine ⟨28698038621201129928414571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153056205979739359618211045 28698038621201129928414571)
  ·
    refine ⟨43047057931801694892621857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28698038621201129928414571 43047057931801694892621857)
    ·
      refine ⟨32285293448851271169466393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43047057931801694892621857 32285293448851271169466393)
      ·
        refine ⟨24213970086638453377099795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32285293448851271169466393 24213970086638453377099795)
        ·
          refine ⟨36320955129957680065649693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24213970086638453377099795 36320955129957680065649693)
          ·
            refine ⟨13620358173734130024618635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36320955129957680065649693 13620358173734130024618635)
            ·
              refine ⟨20430537260601195036927953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13620358173734130024618635 20430537260601195036927953)
              ·
                refine ⟨15322902945450896277695965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20430537260601195036927953 15322902945450896277695965)
                ·
                  refine ⟨5746088604544086104135987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15322902945450896277695965 5746088604544086104135987)
                  ·
                    refine ⟨8619132906816129156203981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5746088604544086104135987 8619132906816129156203981)
                    ·
                      refine ⟨3232174840056048433576493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8619132906816129156203981 3232174840056048433576493)
                      ·
                        rfl

theorem cell23_6294638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_6294638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294638 prefixEnd_6294638 := by exact prefixLift 6294638
  have htrace : WordTrace (prefixWord ++ tailWord_6294638) baseStart_6294638 baseEnd_6294638 := by
    simpa [prefixWord, tailWord_6294638, baseEnd_6294638] using wordTrace_append hprefix tailTrace_6294638
  have hstable : (prefixWord ++ tailWord_6294638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294638).length < 2 ^ (prefixWord ++ tailWord_6294638).sum := by decide
  have hdescent : baseEnd_6294638 < baseStart_6294638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294688 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 2, 4]
def baseStart_6294688 : Nat := 118140960795 + 6294688 * 2 ^ 59
def prefixEnd_6294688 : Nat := 4983230072969 + 3 ^ 40 * 6294688 * 2
def baseEnd_6294688 : Nat := 1077400171362924412650421

theorem tailTrace_6294688 : CollatzResearch.WordTrace tailWord_6294688 prefixEnd_6294688 1077400171362924412650421 := by
  unfold tailWord_6294688
  simp only [CollatzResearch.WordTrace]
  refine ⟨114793066309713948983318359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153057421746285265311091145 114793066309713948983318359)
  ·
    refine ⟨172189599464570923474977539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114793066309713948983318359 172189599464570923474977539)
    ·
      refine ⟨258284399196856385212466309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172189599464570923474977539 258284399196856385212466309)
      ·
        refine ⟨48428324849410572227337433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258284399196856385212466309 48428324849410572227337433)
        ·
          refine ⟨36321243637057929170503075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48428324849410572227337433 36321243637057929170503075)
          ·
            refine ⟨54481865455586893755754613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36321243637057929170503075 54481865455586893755754613)
            ·
              refine ⟨5107674886461271289601995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54481865455586893755754613 5107674886461271289601995)
              ·
                refine ⟨7661512329691906934402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107674886461271289601995 7661512329691906934402993)
                ·
                  refine ⟨5746134247268930200802245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7661512329691906934402993 5746134247268930200802245)
                  ·
                    refine ⟨1077400171362924412650421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5746134247268930200802245 1077400171362924412650421)
                    ·
                      rfl

theorem cell23_6294688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_6294688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294688 prefixEnd_6294688 := by exact prefixLift 6294688
  have htrace : WordTrace (prefixWord ++ tailWord_6294688) baseStart_6294688 baseEnd_6294688 := by
    simpa [prefixWord, tailWord_6294688, baseEnd_6294688] using wordTrace_append hprefix tailTrace_6294688
  have hstable : (prefixWord ++ tailWord_6294688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294688).length < 2 ^ (prefixWord ++ tailWord_6294688).sum := by decide
  have hdescent : baseEnd_6294688 < baseStart_6294688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294695 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_6294695 : Nat := 118140960795 + 6294695 * 2 ^ 59
def prefixEnd_6294695 : Nat := 4983230072969 + 3 ^ 40 * 6294695 * 2
def baseEnd_6294695 : Nat := 3232204108453354710563731

theorem tailTrace_6294695 : CollatzResearch.WordTrace tailWord_6294695 prefixEnd_6294695 3232204108453354710563731 := by
  unfold tailWord_6294695
  simp only [CollatzResearch.WordTrace]
  refine ⟨229586387930402538162141539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153057591953601692108094359 229586387930402538162141539)
  ·
    refine ⟨344379581895603807243212309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229586387930402538162141539 344379581895603807243212309)
    ·
      refine ⟨16142792901356428464525577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 344379581895603807243212309 16142792901356428464525577)
      ·
        refine ⟨12107094676017321348394183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16142792901356428464525577 12107094676017321348394183)
        ·
          refine ⟨18160642014025982022591275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12107094676017321348394183 18160642014025982022591275)
          ·
            refine ⟨27240963021038973033886913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18160642014025982022591275 27240963021038973033886913)
            ·
              refine ⟨20430722265779229775415185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27240963021038973033886913 20430722265779229775415185)
              ·
                refine ⟨15323041699334422331561389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20430722265779229775415185 15323041699334422331561389)
                ·
                  refine ⟨5746140637250408374335521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15323041699334422331561389 5746140637250408374335521)
                  ·
                    refine ⟨4309605477937806280751641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5746140637250408374335521 4309605477937806280751641)
                    ·
                      refine ⟨3232204108453354710563731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309605477937806280751641 3232204108453354710563731)
                      ·
                        rfl

theorem cell23_6294695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_6294695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294695 prefixEnd_6294695 := by exact prefixLift 6294695
  have htrace : WordTrace (prefixWord ++ tailWord_6294695) baseStart_6294695 baseEnd_6294695 := by
    simpa [prefixWord, tailWord_6294695, baseEnd_6294695] using wordTrace_append hprefix tailTrace_6294695
  have hstable : (prefixWord ++ tailWord_6294695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294695).length < 2 ^ (prefixWord ++ tailWord_6294695).sum := by decide
  have hdescent : baseEnd_6294695 < baseStart_6294695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294701 : List Nat := [1, 5, 2, 1, 3, 1, 1, 9]
def baseStart_6294701 : Nat := 118140960795 + 6294701 * 2 ^ 59
def prefixEnd_6294701 : Nat := 4983230072969 + 3 ^ 40 * 6294701 * 2
def baseEnd_6294701 : Nat := 119711377382862284706989

theorem tailTrace_6294701 : CollatzResearch.WordTrace tailWord_6294701 prefixEnd_6294701 119711377382862284706989 := by
  unfold tailWord_6294701
  simp only [CollatzResearch.WordTrace]
  refine ⟨229586606768380801186859957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153057737845587200791239971 229586606768380801186859957)
  ·
    refine ⟨21523744384535700111268121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229586606768380801186859957 21523744384535700111268121)
    ·
      refine ⟨16142808288401775083451091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21523744384535700111268121 16142808288401775083451091)
      ·
        refine ⟨24214212432602662625176637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16142808288401775083451091 24214212432602662625176637)
        ·
          refine ⟨9080329662225998484441239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24214212432602662625176637 9080329662225998484441239)
          ·
            refine ⟨13620494493338997726661859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9080329662225998484441239 13620494493338997726661859)
            ·
              refine ⟨20430741740008496589992789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13620494493338997726661859 20430741740008496589992789)
              ·
                refine ⟨119711377382862284706989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20430741740008496589992789 119711377382862284706989)
                ·
                  rfl

theorem cell23_6294701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 9].length) (baseStart_6294701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294701 prefixEnd_6294701 := by exact prefixLift 6294701
  have htrace : WordTrace (prefixWord ++ tailWord_6294701) baseStart_6294701 baseEnd_6294701 := by
    simpa [prefixWord, tailWord_6294701, baseEnd_6294701] using wordTrace_append hprefix tailTrace_6294701
  have hstable : (prefixWord ++ tailWord_6294701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294701).length < 2 ^ (prefixWord ++ tailWord_6294701).sum := by decide
  have hdescent : baseEnd_6294701 < baseStart_6294701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294711 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_6294711 : Nat := 118140960795 + 6294711 * 2 ^ 59
def prefixEnd_6294711 : Nat := 4983230072969 + 3 ^ 40 * 6294711 * 2
def baseEnd_6294711 : Nat := 3232212324143826647963657

theorem tailTrace_6294711 : CollatzResearch.WordTrace tailWord_6294711 prefixEnd_6294711 3232212324143826647963657 := by
  unfold tailWord_6294711
  simp only [CollatzResearch.WordTrace]
  refine ⟨229586971498344572894723987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153057980998896381929815991 229586971498344572894723987)
  ·
    refine ⟨344380457247516859342085981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229586971498344572894723987 344380457247516859342085981)
    ·
      refine ⟨129142671467818822253282243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344380457247516859342085981 129142671467818822253282243)
      ·
        refine ⟨193714007201728233379923365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129142671467818822253282243 193714007201728233379923365)
        ·
          refine ⟨36321376350324043758735631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193714007201728233379923365 36321376350324043758735631)
          ·
            refine ⟨54482064525486065638103447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36321376350324043758735631 54482064525486065638103447)
            ·
              refine ⟨81723096788229098457155171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54482064525486065638103447 81723096788229098457155171)
              ·
                refine ⟨122584645182343647685732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81723096788229098457155171 122584645182343647685732757)
                ·
                  refine ⟨5746155242922358485268723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122584645182343647685732757 5746155242922358485268723)
                  ·
                    refine ⟨8619232864383537727903085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5746155242922358485268723 8619232864383537727903085)
                    ·
                      refine ⟨3232212324143826647963657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8619232864383537727903085 3232212324143826647963657)
                      ·
                        rfl

theorem cell23_6294711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_6294711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294711 prefixEnd_6294711 := by exact prefixLift 6294711
  have htrace : WordTrace (prefixWord ++ tailWord_6294711) baseStart_6294711 baseEnd_6294711 := by
    simpa [prefixWord, tailWord_6294711, baseEnd_6294711] using wordTrace_append hprefix tailTrace_6294711
  have hstable : (prefixWord ++ tailWord_6294711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294711).length < 2 ^ (prefixWord ++ tailWord_6294711).sum := by decide
  have hdescent : baseEnd_6294711 < baseStart_6294711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294738 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6294738 : Nat := 118140960795 + 6294738 * 2 ^ 59
def prefixEnd_6294738 : Nat := 4983230072969 + 3 ^ 40 * 6294738 * 2
def baseEnd_6294738 : Nat := 3232226188121498042326033

theorem tailTrace_6294738 : CollatzResearch.WordTrace tailWord_6294738 prefixEnd_6294738 3232226188121498042326033 := by
  unfold tailWord_6294738
  simp only [CollatzResearch.WordTrace]
  refine ⟨57396989067311689126489217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153058637512831171003971245 57396989067311689126489217)
  ·
    refine ⟨43047741800483766844866913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57396989067311689126489217 43047741800483766844866913)
    ·
      refine ⟨32285806350362825133650185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43047741800483766844866913 32285806350362825133650185)
      ·
        refine ⟨24214354762772118850237639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32285806350362825133650185 24214354762772118850237639)
        ·
          refine ⟨36321532144158178275356459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24214354762772118850237639 36321532144158178275356459)
          ·
            refine ⟨54482298216237267413034689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36321532144158178275356459 54482298216237267413034689)
            ·
              refine ⟨40861723662177950559776017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54482298216237267413034689 40861723662177950559776017)
              ·
                refine ⟨30646292746633462919832013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40861723662177950559776017 30646292746633462919832013)
                ·
                  refine ⟨11492359779987548594937005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30646292746633462919832013 11492359779987548594937005)
                  ·
                    refine ⟨4309634917495330723101377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11492359779987548594937005 4309634917495330723101377)
                    ·
                      refine ⟨3232226188121498042326033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309634917495330723101377 3232226188121498042326033)
                      ·
                        rfl

theorem cell23_6294738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6294738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294738 prefixEnd_6294738 := by exact prefixLift 6294738
  have htrace : WordTrace (prefixWord ++ tailWord_6294738) baseStart_6294738 baseEnd_6294738 := by
    simpa [prefixWord, tailWord_6294738, baseEnd_6294738] using wordTrace_append hprefix tailTrace_6294738
  have hstable : (prefixWord ++ tailWord_6294738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294738).length < 2 ^ (prefixWord ++ tailWord_6294738).sum := by decide
  have hdescent : baseEnd_6294738 < baseStart_6294738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294785 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_6294785 : Nat := 118140960795 + 6294785 * 2 ^ 59
def prefixEnd_6294785 : Nat := 4983230072969 + 3 ^ 40 * 6294785 * 2
def baseEnd_6294785 : Nat := 3232250321712259358438317

theorem tailTrace_6294785 : CollatzResearch.WordTrace tailWord_6294785 prefixEnd_6294785 3232250321712259358438317 := by
  unfold tailWord_6294785
  simp only [CollatzResearch.WordTrace]
  refine ⟨229589670500076483532917809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153059780333384322355278539 229589670500076483532917809)
  ·
    refine ⟨172192252875057362649688357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229589670500076483532917809 172192252875057362649688357)
    ·
      refine ⟨32286047414073255496816567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172192252875057362649688357 32286047414073255496816567)
      ·
        refine ⟨48429071121109883245224851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32286047414073255496816567 48429071121109883245224851)
        ·
          refine ⟨72643606681664824867837277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48429071121109883245224851 72643606681664824867837277)
          ·
            refine ⟨27241352505624309325438979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72643606681664824867837277 27241352505624309325438979)
            ·
              refine ⟨40862028758436463988158469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27241352505624309325438979 40862028758436463988158469)
              ·
                refine ⟨7661630392206836997779713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40862028758436463988158469 7661630392206836997779713)
                ·
                  refine ⟨5746222794155127748334785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7661630392206836997779713 5746222794155127748334785)
                  ·
                    refine ⟨4309667095616345811251089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5746222794155127748334785 4309667095616345811251089)
                    ·
                      refine ⟨3232250321712259358438317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309667095616345811251089 3232250321712259358438317)
                      ·
                        rfl

theorem cell23_6294785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_6294785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294785 prefixEnd_6294785 := by exact prefixLift 6294785
  have htrace : WordTrace (prefixWord ++ tailWord_6294785) baseStart_6294785 baseEnd_6294785 := by
    simpa [prefixWord, tailWord_6294785, baseEnd_6294785] using wordTrace_append hprefix tailTrace_6294785
  have hstable : (prefixWord ++ tailWord_6294785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294785).length < 2 ^ (prefixWord ++ tailWord_6294785).sum := by decide
  have hdescent : baseEnd_6294785 < baseStart_6294785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294794 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6294794 : Nat := 118140960795 + 6294794 * 2 ^ 59
def prefixEnd_6294794 : Nat := 4983230072969 + 3 ^ 40 * 6294794 * 2
def baseEnd_6294794 : Nat := 3232254943038149823225775

theorem tailTrace_6294794 : CollatzResearch.WordTrace tailWord_6294794 prefixEnd_6294794 3232254943038149823225775 := by
  unfold tailWord_6294794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57397499689260969517498859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153059999171362585379996957 57397499689260969517498859)
  ·
    refine ⟨86096249533891454276248289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57397499689260969517498859 86096249533891454276248289)
    ·
      refine ⟨64572187150418590707186217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86096249533891454276248289 64572187150418590707186217)
      ·
        refine ⟨48429140362813943030389663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64572187150418590707186217 48429140362813943030389663)
        ·
          refine ⟨72643710544220914545584495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48429140362813943030389663 72643710544220914545584495)
          ·
            refine ⟨108965565816331371818376743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72643710544220914545584495 108965565816331371818376743)
            ·
              refine ⟨163448348724497057727565115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108965565816331371818376743 163448348724497057727565115)
              ·
                refine ⟨245172523086745586591347673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163448348724497057727565115 245172523086745586591347673)
                ·
                  refine ⟨183879392315059189943510755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245172523086745586591347673 183879392315059189943510755)
                  ·
                    refine ⟨275819088472588784915266133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183879392315059189943510755 275819088472588784915266133)
                    ·
                      refine ⟨3232254943038149823225775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275819088472588784915266133 3232254943038149823225775)
                      ·
                        rfl

theorem cell23_6294794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6294794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294794 prefixEnd_6294794 := by exact prefixLift 6294794
  have htrace : WordTrace (prefixWord ++ tailWord_6294794) baseStart_6294794 baseEnd_6294794 := by
    simpa [prefixWord, tailWord_6294794, baseEnd_6294794] using wordTrace_append hprefix tailTrace_6294794
  have hstable : (prefixWord ++ tailWord_6294794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294794).length < 2 ^ (prefixWord ++ tailWord_6294794).sum := by decide
  have hdescent : baseEnd_6294794 < baseStart_6294794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294801 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_6294801 : Nat := 118140960795 + 6294801 * 2 ^ 59
def prefixEnd_6294801 : Nat := 4983230072969 + 3 ^ 40 * 6294801 * 2
def baseEnd_6294801 : Nat := 3232258537402731295838243

theorem tailTrace_6294801 : CollatzResearch.WordTrace tailWord_6294801 prefixEnd_6294801 3232258537402731295838243 := by
  unfold tailWord_6294801
  simp only [CollatzResearch.WordTrace]
  refine ⟨229590254068018518265500257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153060169378679012177000171 229590254068018518265500257)
  ·
    refine ⟨172192690551013888699125193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229590254068018518265500257 172192690551013888699125193)
    ·
      refine ⟨129144517913260416524343895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172192690551013888699125193 129144517913260416524343895)
      ·
        refine ⟨193716776869890624786515843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129144517913260416524343895 193716776869890624786515843)
        ·
          refine ⟨290575165304835937179773765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193716776869890624786515843 290575165304835937179773765)
          ·
            refine ⟨54482843494656738221207581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290575165304835937179773765 54482843494656738221207581)
            ·
              refine ⟨20431066310496276832952843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54482843494656738221207581 20431066310496276832952843)
              ·
                refine ⟨30646599465744415249429265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20431066310496276832952843 30646599465744415249429265)
                ·
                  refine ⟨22984949599308311437071949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30646599465744415249429265 22984949599308311437071949)
                  ·
                    refine ⟨8619356099740616788901981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22984949599308311437071949 8619356099740616788901981)
                    ·
                      refine ⟨3232258537402731295838243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8619356099740616788901981 3232258537402731295838243)
                      ·
                        rfl

theorem cell23_6294801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_6294801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294801 prefixEnd_6294801 := by exact prefixLift 6294801
  have htrace : WordTrace (prefixWord ++ tailWord_6294801) baseStart_6294801 baseEnd_6294801 := by
    simpa [prefixWord, tailWord_6294801, baseEnd_6294801] using wordTrace_append hprefix tailTrace_6294801
  have hstable : (prefixWord ++ tailWord_6294801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294801).length < 2 ^ (prefixWord ++ tailWord_6294801).sum := by decide
  have hdescent : baseEnd_6294801 < baseStart_6294801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294811 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 5, 2]
def baseStart_6294811 : Nat := 118140960795 + 6294811 * 2 ^ 59
def prefixEnd_6294811 : Nat := 4983230072969 + 3 ^ 40 * 6294811 * 2
def baseEnd_6294811 : Nat := 3232263672209276256713197

theorem tailTrace_6294811 : CollatzResearch.WordTrace tailWord_6294811 prefixEnd_6294811 3232263672209276256713197 := by
  unfold tailWord_6294811
  simp only [CollatzResearch.WordTrace]
  refine ⟨229590618797982289973364287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153060412531988193315576191 229590618797982289973364287)
  ·
    refine ⟨344385928196973434960046431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229590618797982289973364287 344385928196973434960046431)
    ·
      refine ⟨516578892295460152440069647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344385928196973434960046431 516578892295460152440069647)
      ·
        refine ⟨774868338443190228660104471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516578892295460152440069647 774868338443190228660104471)
        ·
          refine ⟨1162302507664785342990156707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774868338443190228660104471 1162302507664785342990156707)
          ·
            refine ⟨1743453761497178014485235061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162302507664785342990156707 1743453761497178014485235061)
            ·
              refine ⟨163448790140360438857990787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1743453761497178014485235061 163448790140360438857990787)
              ·
                refine ⟨245173185210540658286986181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163448790140360438857990787 245173185210540658286986181)
                ·
                  refine ⟨45969972226976373428809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245173185210540658286986181 45969972226976373428809909)
                  ·
                    refine ⟨4309684896279035008950929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45969972226976373428809909 4309684896279035008950929)
                    ·
                      refine ⟨3232263672209276256713197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309684896279035008950929 3232263672209276256713197)
                      ·
                        rfl

theorem cell23_6294811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5, 2].length) (baseStart_6294811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294811 prefixEnd_6294811 := by exact prefixLift 6294811
  have htrace : WordTrace (prefixWord ++ tailWord_6294811) baseStart_6294811 baseEnd_6294811 := by
    simpa [prefixWord, tailWord_6294811, baseEnd_6294811] using wordTrace_append hprefix tailTrace_6294811
  have hstable : (prefixWord ++ tailWord_6294811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294811).length < 2 ^ (prefixWord ++ tailWord_6294811).sum := by decide
  have hdescent : baseEnd_6294811 < baseStart_6294811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294821 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_6294821 : Nat := 118140960795 + 6294821 * 2 ^ 59
def prefixEnd_6294821 : Nat := 4983230072969 + 3 ^ 40 * 6294821 * 2
def baseEnd_6294821 : Nat := 1077422935671940405862717

theorem tailTrace_6294821 : CollatzResearch.WordTrace tailWord_6294821 prefixEnd_6294821 1077422935671940405862717 := by
  unfold tailWord_6294821
  simp only [CollatzResearch.WordTrace]
  refine ⟨229590983527946061681228317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153060655685297374454152211 229590983527946061681228317)
  ·
    refine ⟨86096618822979773130460619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229590983527946061681228317 86096618822979773130460619)
    ·
      refine ⟨129144928234469659695690929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86096618822979773130460619 129144928234469659695690929)
      ·
        refine ⟨96858696175852244771768197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129144928234469659695690929 96858696175852244771768197)
        ·
          refine ⟨18161005532972295894706537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96858696175852244771768197 18161005532972295894706537)
          ·
            refine ⟨13620754149729221921029903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18161005532972295894706537 13620754149729221921029903)
            ·
              refine ⟨20431131224593832881544855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13620754149729221921029903 20431131224593832881544855)
              ·
                refine ⟨30646696836890749322317283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20431131224593832881544855 30646696836890749322317283)
                ·
                  refine ⟨45970045255336123983475925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30646696836890749322317283 45970045255336123983475925)
                  ·
                    refine ⟨1077422935671940405862717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45970045255336123983475925 1077422935671940405862717)
                    ·
                      rfl

theorem cell23_6294821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_6294821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294821 prefixEnd_6294821 := by exact prefixLift 6294821
  have htrace : WordTrace (prefixWord ++ tailWord_6294821) baseStart_6294821 baseEnd_6294821 := by
    simpa [prefixWord, tailWord_6294821, baseEnd_6294821] using wordTrace_append hprefix tailTrace_6294821
  have hstable : (prefixWord ++ tailWord_6294821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294821).length < 2 ^ (prefixWord ++ tailWord_6294821).sum := by decide
  have hdescent : baseEnd_6294821 < baseStart_6294821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294868 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_6294868 : Nat := 118140960795 + 6294868 * 2 ^ 59
def prefixEnd_6294868 : Nat := 4983230072969 + 3 ^ 40 * 6294868 * 2
def baseEnd_6294868 : Nat := 1077430980202194177900145

theorem tailTrace_6294868 : CollatzResearch.WordTrace tailWord_6294868 prefixEnd_6294868 1077430980202194177900145 := by
  unfold tailWord_6294868
  simp only [CollatzResearch.WordTrace]
  refine ⟨114796348879387894354094629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153061798505850525805459505 114796348879387894354094629)
  ·
    refine ⟨21524315414885230191392743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114796348879387894354094629 21524315414885230191392743)
    ·
      refine ⟨32286473122327845287089115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21524315414885230191392743 32286473122327845287089115)
      ·
        refine ⟨48429709683491767930633673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32286473122327845287089115 48429709683491767930633673)
        ·
          refine ⟨36322282262618825947975255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48429709683491767930633673 36322282262618825947975255)
          ·
            refine ⟨54483423393928238921962883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36322282262618825947975255 54483423393928238921962883)
            ·
              refine ⟨81725135090892358382944325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54483423393928238921962883 81725135090892358382944325)
              ·
                refine ⟨15323462829542317196802061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81725135090892358382944325 15323462829542317196802061)
                ·
                  refine ⟨5746298561078368948800773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15323462829542317196802061 5746298561078368948800773)
                  ·
                    refine ⟨1077430980202194177900145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5746298561078368948800773 1077430980202194177900145)
                    ·
                      rfl

theorem cell23_6294868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_6294868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294868 prefixEnd_6294868 := by exact prefixLift 6294868
  have htrace : WordTrace (prefixWord ++ tailWord_6294868) baseStart_6294868 baseEnd_6294868 := by
    simpa [prefixWord, tailWord_6294868, baseEnd_6294868] using wordTrace_append hprefix tailTrace_6294868
  have hstable : (prefixWord ++ tailWord_6294868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294868).length < 2 ^ (prefixWord ++ tailWord_6294868).sum := by decide
  have hdescent : baseEnd_6294868 < baseStart_6294868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294915 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 6]
def baseStart_6294915 : Nat := 118140960795 + 6294915 * 2 ^ 59
def prefixEnd_6294915 : Nat := 4983230072969 + 3 ^ 40 * 6294915 * 2
def baseEnd_6294915 : Nat := 359146341577482649979191

theorem tailTrace_6294915 : CollatzResearch.WordTrace tailWord_6294915 prefixEnd_6294915 359146341577482649979191 := by
  unfold tailWord_6294915
  simp only [CollatzResearch.WordTrace]
  refine ⟨229594411989605515735150199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153062941326403677156766799 229594411989605515735150199)
  ·
    refine ⟨344391617984408273602725299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229594411989605515735150199 344391617984408273602725299)
    ·
      refine ⟨516587426976612410404087949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344391617984408273602725299 516587426976612410404087949)
      ·
        refine ⟨193720285116229653901532981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516587426976612410404087949 193720285116229653901532981)
        ·
          refine ⟨18161276729646530053268717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193720285116229653901532981 18161276729646530053268717)
          ·
            refine ⟨6810478773617448769975769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18161276729646530053268717 6810478773617448769975769)
            ·
              refine ⟨5107859080213086577481827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810478773617448769975769 5107859080213086577481827)
              ·
                refine ⟨7661788620319629866222741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107859080213086577481827 7661788620319629866222741)
                ·
                  refine ⟨359146341577482649979191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7661788620319629866222741 359146341577482649979191)
                  ·
                    rfl

theorem cell23_6294915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 6].length) (baseStart_6294915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294915 prefixEnd_6294915 := by exact prefixLift 6294915
  have htrace : WordTrace (prefixWord ++ tailWord_6294915) baseStart_6294915 baseEnd_6294915 := by
    simpa [prefixWord, tailWord_6294915, baseEnd_6294915] using wordTrace_append hprefix tailTrace_6294915
  have hstable : (prefixWord ++ tailWord_6294915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294915).length < 2 ^ (prefixWord ++ tailWord_6294915).sum := by decide
  have hdescent : baseEnd_6294915 < baseStart_6294915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6294968 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_6294968 : Nat := 118140960795 + 6294968 * 2 ^ 59
def prefixEnd_6294968 : Nat := 4983230072969 + 3 ^ 40 * 6294968 * 2
def baseEnd_6294968 : Nat := 3232344288672032142449975

theorem tailTrace_6294968 : CollatzResearch.WordTrace tailWord_6294968 prefixEnd_6294968 3232344288672032142449975 := by
  unfold tailWord_6294968
  simp only [CollatzResearch.WordTrace]
  refine ⟨114798172529206752893414779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153064230038942337191219705 114798172529206752893414779)
  ·
    refine ⟨172197258793810129340122169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114798172529206752893414779 172197258793810129340122169)
    ·
      refine ⟨129147944095357597005091627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172197258793810129340122169 129147944095357597005091627)
      ·
        refine ⟨193721916143036395507637441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129147944095357597005091627 193721916143036395507637441)
        ·
          refine ⟨145291437107277296630728081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193721916143036395507637441 145291437107277296630728081)
          ·
            refine ⟨108968577830457972473046061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145291437107277296630728081 108968577830457972473046061)
            ·
              refine ⟨40863216686421739677392273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108968577830457972473046061 40863216686421739677392273)
              ·
                refine ⟨30647412514816304758044205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40863216686421739677392273 30647412514816304758044205)
                ·
                  refine ⟨11492779693056114284266577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30647412514816304758044205 11492779693056114284266577)
                  ·
                    refine ⟨8619584769792085713199933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11492779693056114284266577 8619584769792085713199933)
                    ·
                      refine ⟨3232344288672032142449975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8619584769792085713199933 3232344288672032142449975)
                      ·
                        rfl

theorem cell23_6294968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_6294968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6294968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6294968 prefixEnd_6294968 := by exact prefixLift 6294968
  have htrace : WordTrace (prefixWord ++ tailWord_6294968) baseStart_6294968 baseEnd_6294968 := by
    simpa [prefixWord, tailWord_6294968, baseEnd_6294968] using wordTrace_append hprefix tailTrace_6294968
  have hstable : (prefixWord ++ tailWord_6294968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6294968).length < 2 ^ (prefixWord ++ tailWord_6294968).sum := by decide
  have hdescent : baseEnd_6294968 < baseStart_6294968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6294968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295002 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_6295002 : Nat := 118140960795 + 6295002 * 2 ^ 59
def prefixEnd_6295002 : Nat := 4983230072969 + 3 ^ 40 * 6295002 * 2
def baseEnd_6295002 : Nat := 3232361747014285009424819

theorem tailTrace_6295002 : CollatzResearch.WordTrace tailWord_6295002 prefixEnd_6295002 3232361747014285009424819 := by
  unfold tailWord_6295002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57399396285072582398391815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153065056760193553062378173 57399396285072582398391815)
  ·
    refine ⟨86099094427608873597587723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57399396285072582398391815 86099094427608873597587723)
    ·
      refine ⟨129148641641413310396381585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86099094427608873597587723 129148641641413310396381585)
      ·
        refine ⟨96861481231059982797286189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129148641641413310396381585 96861481231059982797286189)
        ·
          refine ⟨36323055461647493548982321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96861481231059982797286189 36323055461647493548982321)
          ·
            refine ⟨27242291596235620161736741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36323055461647493548982321 27242291596235620161736741)
            ·
              refine ⟨5107929674294178780325639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27242291596235620161736741 5107929674294178780325639)
              ·
                refine ⟨7661894511441268170488459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107929674294178780325639 7661894511441268170488459)
                ·
                  refine ⟨11492841767161902255732689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7661894511441268170488459 11492841767161902255732689)
                  ·
                    refine ⟨8619631325371426691799517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11492841767161902255732689 8619631325371426691799517)
                    ·
                      refine ⟨3232361747014285009424819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8619631325371426691799517 3232361747014285009424819)
                      ·
                        rfl

theorem cell23_6295002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_6295002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295002 prefixEnd_6295002 := by exact prefixLift 6295002
  have htrace : WordTrace (prefixWord ++ tailWord_6295002) baseStart_6295002 baseEnd_6295002 := by
    simpa [prefixWord, tailWord_6295002, baseEnd_6295002] using wordTrace_append hprefix tailTrace_6295002
  have hstable : (prefixWord ++ tailWord_6295002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295002).length < 2 ^ (prefixWord ++ tailWord_6295002).sum := by decide
  have hdescent : baseEnd_6295002 < baseStart_6295002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295031 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 8]
def baseStart_6295031 : Nat := 118140960795 + 6295031 * 2 ^ 59
def prefixEnd_6295031 : Nat := 4983230072969 + 3 ^ 40 * 6295031 * 2
def baseEnd_6295031 : Nat := 1077458879317755131987395

theorem tailTrace_6295031 : CollatzResearch.WordTrace tailWord_6295031 prefixEnd_6295031 1077458879317755131987395 := by
  unfold tailWord_6295031
  simp only [CollatzResearch.WordTrace]
  refine ⟨229598642857185267546372947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153065761904790178364248631 229598642857185267546372947)
  ·
    refine ⟨344397964285777901319559421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229598642857185267546372947 344397964285777901319559421)
    ·
      refine ⟨129149236607166712994834783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344397964285777901319559421 129149236607166712994834783)
      ·
        refine ⟨193723854910750069492252175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129149236607166712994834783 193723854910750069492252175)
        ·
          refine ⟨290585782366125104238378263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193723854910750069492252175 290585782366125104238378263)
          ·
            refine ⟨435878673549187656357567395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290585782366125104238378263 435878673549187656357567395)
            ·
              refine ⟨653818010323781484536351093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435878673549187656357567395 653818010323781484536351093)
              ·
                refine ⟨61295438467854514175282915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653818010323781484536351093 61295438467854514175282915)
                ·
                  refine ⟨91943157701781771262924373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61295438467854514175282915 91943157701781771262924373)
                  ·
                    refine ⟨1077458879317755131987395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91943157701781771262924373 1077458879317755131987395)
                    ·
                      rfl

theorem cell23_6295031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_6295031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295031 prefixEnd_6295031 := by exact prefixLift 6295031
  have htrace : WordTrace (prefixWord ++ tailWord_6295031) baseStart_6295031 baseEnd_6295031 := by
    simpa [prefixWord, tailWord_6295031, baseEnd_6295031] using wordTrace_append hprefix tailTrace_6295031
  have hstable : (prefixWord ++ tailWord_6295031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295031).length < 2 ^ (prefixWord ++ tailWord_6295031).sum := by decide
  have hdescent : baseEnd_6295031 < baseStart_6295031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295088 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_6295088 : Nat := 118140960795 + 6295088 * 2 ^ 59
def prefixEnd_6295088 : Nat := 4983230072969 + 3 ^ 40 * 6295088 * 2
def baseEnd_6295088 : Nat := 3232405906350571672949423

theorem tailTrace_6295088 : CollatzResearch.WordTrace tailWord_6295088 prefixEnd_6295088 3232405906350571672949423 := by
  unfold tailWord_6295088
  simp only [CollatzResearch.WordTrace]
  refine ⟨114800360908989383140598959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153067147878652510854131945 114800360908989383140598959)
  ·
    refine ⟨172200541363484074710898439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114800360908989383140598959 172200541363484074710898439)
    ·
      refine ⟨258300812045226112066347659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172200541363484074710898439 258300812045226112066347659)
      ·
        refine ⟨387451218067839168099521489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258300812045226112066347659 387451218067839168099521489)
        ·
          refine ⟨290588413550879376074641117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387451218067839168099521489 290588413550879376074641117)
          ·
            refine ⟨108970655081579766027990419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290588413550879376074641117 108970655081579766027990419)
            ·
              refine ⟨163455982622369649041985629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108970655081579766027990419 163455982622369649041985629)
              ·
                refine ⟨61295993483388618390744611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163455982622369649041985629 61295993483388618390744611)
                ·
                  refine ⟨91943990225082927586116917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61295993483388618390744611 91943990225082927586116917)
                  ·
                    refine ⟨8619749083601524461198461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91943990225082927586116917 8619749083601524461198461)
                    ·
                      refine ⟨3232405906350571672949423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8619749083601524461198461 3232405906350571672949423)
                      ·
                        rfl

theorem cell23_6295088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_6295088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295088 prefixEnd_6295088 := by exact prefixLift 6295088
  have htrace : WordTrace (prefixWord ++ tailWord_6295088) baseStart_6295088 baseEnd_6295088 := by
    simpa [prefixWord, tailWord_6295088, baseEnd_6295088] using wordTrace_append hprefix tailTrace_6295088
  have hstable : (prefixWord ++ tailWord_6295088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295088).length < 2 ^ (prefixWord ++ tailWord_6295088).sum := by decide
  have hdescent : baseEnd_6295088 < baseStart_6295088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295128 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6295128 : Nat := 118140960795 + 6295128 * 2 ^ 59
def prefixEnd_6295128 : Nat := 4983230072969 + 3 ^ 40 * 6295128 * 2
def baseEnd_6295128 : Nat := 3232426445576751516449239

theorem tailTrace_6295128 : CollatzResearch.WordTrace tailWord_6295128 prefixEnd_6295128 3232426445576751516449239 := by
  unfold tailWord_6295128
  simp only [CollatzResearch.WordTrace]
  refine ⟨114801090368916926556327019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153068120491889235408436025 114801090368916926556327019)
  ·
    refine ⟨172201635553375389834490529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114801090368916926556327019 172201635553375389834490529)
    ·
      refine ⟨129151226665031542375867897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172201635553375389834490529 129151226665031542375867897)
      ·
        refine ⟨96863419998773656781900923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129151226665031542375867897 96863419998773656781900923)
        ·
          refine ⟨145295129998160485172851385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96863419998773656781900923 145295129998160485172851385)
          ·
            refine ⟨108971347498620363879638539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145295129998160485172851385 108971347498620363879638539)
            ·
              refine ⟨163457021247930545819457809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108971347498620363879638539 163457021247930545819457809)
              ·
                refine ⟨122592765935947909364593357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163457021247930545819457809 122592765935947909364593357)
                ·
                  refine ⟨45972287225980466011722509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122592765935947909364593357 45972287225980466011722509)
                  ·
                    refine ⟨17239607709742674754395941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45972287225980466011722509 17239607709742674754395941)
                    ·
                      refine ⟨3232426445576751516449239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17239607709742674754395941 3232426445576751516449239)
                      ·
                        rfl

theorem cell23_6295128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6295128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295128 prefixEnd_6295128 := by exact prefixLift 6295128
  have htrace : WordTrace (prefixWord ++ tailWord_6295128) baseStart_6295128 baseEnd_6295128 := by
    simpa [prefixWord, tailWord_6295128, baseEnd_6295128] using wordTrace_append hprefix tailTrace_6295128
  have hstable : (prefixWord ++ tailWord_6295128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295128).length < 2 ^ (prefixWord ++ tailWord_6295128).sum := by decide
  have hdescent : baseEnd_6295128 < baseStart_6295128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295132 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_6295132 : Nat := 118140960795 + 6295132 * 2 ^ 59
def prefixEnd_6295132 : Nat := 4983230072969 + 3 ^ 40 * 6295132 * 2
def baseEnd_6295132 : Nat := 3232428499499369500799221

theorem tailTrace_6295132 : CollatzResearch.WordTrace tailWord_6295132 prefixEnd_6295132 3232428499499369500799221 := by
  unfold tailWord_6295132
  simp only [CollatzResearch.WordTrace]
  refine ⟨114801163314909680897899825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153068217753212907863866433 114801163314909680897899825)
  ·
    refine ⟨86100872486182260673424869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114801163314909680897899825 86100872486182260673424869)
    ·
      refine ⟨16143913591159173876267163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86100872486182260673424869 16143913591159173876267163)
      ·
        refine ⟨24215870386738760814400745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16143913591159173876267163 24215870386738760814400745)
        ·
          refine ⟨18161902790054070610800559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24215870386738760814400745 18161902790054070610800559)
          ·
            refine ⟨27242854185081105916200839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18161902790054070610800559 27242854185081105916200839)
            ·
              refine ⟨40864281277621658874301259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27242854185081105916200839 40864281277621658874301259)
              ·
                refine ⟨61296421916432488311451889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40864281277621658874301259 61296421916432488311451889)
                ·
                  refine ⟨45972316437324366233588917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61296421916432488311451889 45972316437324366233588917)
                  ·
                    refine ⟨4309904665999159334398961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45972316437324366233588917 4309904665999159334398961)
                    ·
                      refine ⟨3232428499499369500799221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309904665999159334398961 3232428499499369500799221)
                      ·
                        rfl

theorem cell23_6295132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_6295132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295132 prefixEnd_6295132 := by exact prefixLift 6295132
  have htrace : WordTrace (prefixWord ++ tailWord_6295132) baseStart_6295132 baseEnd_6295132 := by
    simpa [prefixWord, tailWord_6295132, baseEnd_6295132] using wordTrace_append hprefix tailTrace_6295132
  have hstable : (prefixWord ++ tailWord_6295132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295132).length < 2 ^ (prefixWord ++ tailWord_6295132).sum := by decide
  have hdescent : baseEnd_6295132 < baseStart_6295132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295145 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 6, 2]
def baseStart_6295145 : Nat := 118140960795 + 6295145 * 2 ^ 59
def prefixEnd_6295145 : Nat := 4983230072969 + 3 ^ 40 * 6295145 * 2
def baseEnd_6295145 : Nat := 3232435174747877949936661

theorem tailTrace_6295145 : CollatzResearch.WordTrace tailWord_6295145 prefixEnd_6295145 3232435174747877949936661 := by
  unfold tailWord_6295145
  simp only [CollatzResearch.WordTrace]
  refine ⟨229602800778772265016022889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153068533852514843344015259 229602800778772265016022889)
  ·
    refine ⟨172202100584079198762017167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229602800778772265016022889 172202100584079198762017167)
    ·
      refine ⟨258303150876118798143025751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172202100584079198762017167 258303150876118798143025751)
      ·
        refine ⟨387454726314178197214538627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258303150876118798143025751 387454726314178197214538627)
        ·
          refine ⟨581182089471267295821807941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387454726314178197214538627 581182089471267295821807941)
          ·
            refine ⟨108971641775862617966588989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 581182089471267295821807941 108971641775862617966588989)
            ·
              refine ⟨40864365665948481737470871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108971641775862617966588989 40864365665948481737470871)
              ·
                refine ⟨61296548498922722606206307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40864365665948481737470871 61296548498922722606206307)
                ·
                  refine ⟨91944822748384083909309461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61296548498922722606206307 91944822748384083909309461)
                  ·
                    refine ⟨4309913566330503933248881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91944822748384083909309461 4309913566330503933248881)
                    ·
                      refine ⟨3232435174747877949936661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309913566330503933248881 3232435174747877949936661)
                      ·
                        rfl

theorem cell23_6295145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6, 2].length) (baseStart_6295145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295145 prefixEnd_6295145 := by exact prefixLift 6295145
  have htrace : WordTrace (prefixWord ++ tailWord_6295145) baseStart_6295145 baseEnd_6295145 := by
    simpa [prefixWord, tailWord_6295145, baseEnd_6295145] using wordTrace_append hprefix tailTrace_6295145
  have hstable : (prefixWord ++ tailWord_6295145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295145).length < 2 ^ (prefixWord ++ tailWord_6295145).sum := by decide
  have hdescent : baseEnd_6295145 < baseStart_6295145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295168 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 8]
def baseStart_6295168 : Nat := 118140960795 + 6295168 * 2 ^ 59
def prefixEnd_6295168 : Nat := 4983230072969 + 3 ^ 40 * 6295168 * 2
def baseEnd_6295168 : Nat := 359160776089214595549895

theorem tailTrace_6295168 : CollatzResearch.WordTrace tailWord_6295168 prefixEnd_6295168 359160776089214595549895 := by
  unfold tailWord_6295168
  simp only [CollatzResearch.WordTrace]
  refine ⟨114801819828844469972055079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153069093105125959962740105 114801819828844469972055079)
  ·
    refine ⟨172202729743266704958082619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114801819828844469972055079 172202729743266704958082619)
    ·
      refine ⟨258304094614900057437123929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172202729743266704958082619 258304094614900057437123929)
      ·
        refine ⟨193728070961175043077842947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258304094614900057437123929 193728070961175043077842947)
        ·
          refine ⟨290592106441762564616764421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193728070961175043077842947 290592106441762564616764421)
          ·
            refine ⟨54486019957830480865643329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290592106441762564616764421 54486019957830480865643329)
            ·
              refine ⟨40864514968372860649232497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54486019957830480865643329 40864514968372860649232497)
              ·
                refine ⟨30648386226279645486924373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40864514968372860649232497 30648386226279645486924373)
                ·
                  refine ⟨359160776089214595549895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30648386226279645486924373 359160776089214595549895)
                  ·
                    rfl

theorem cell23_6295168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_6295168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295168 prefixEnd_6295168 := by exact prefixLift 6295168
  have htrace : WordTrace (prefixWord ++ tailWord_6295168) baseStart_6295168 baseEnd_6295168 := by
    simpa [prefixWord, tailWord_6295168, baseEnd_6295168] using wordTrace_append hprefix tailTrace_6295168
  have hstable : (prefixWord ++ tailWord_6295168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295168).length < 2 ^ (prefixWord ++ tailWord_6295168).sum := by decide
  have hdescent : baseEnd_6295168 < baseStart_6295168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295255 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_6295255 : Nat := 118140960795 + 6295255 * 2 ^ 59
def prefixEnd_6295255 : Nat := 4983230072969 + 3 ^ 40 * 6295255 * 2
def baseEnd_6295255 : Nat := 3232491657619872519561155

theorem tailTrace_6295255 : CollatzResearch.WordTrace tailWord_6295255 prefixEnd_6295255 3232491657619872519561155 := by
  unfold tailWord_6295255
  simp only [CollatzResearch.WordTrace]
  refine ⟨229606812808373753802527219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153071208538915835868351479 229606812808373753802527219)
  ·
    refine ⟨344410219212560630703790829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229606812808373753802527219 344410219212560630703790829)
    ·
      refine ⟨129153832204710236513921561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344410219212560630703790829 129153832204710236513921561)
      ·
        refine ⟨96865374153532677385441171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129153832204710236513921561 96865374153532677385441171)
        ·
          refine ⟨145298061230299016078161757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96865374153532677385441171 145298061230299016078161757)
          ·
            refine ⟨54486772961362131029310659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145298061230299016078161757 54486772961362131029310659)
            ·
              refine ⟨81730159442043196543965989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54486772961362131029310659 81730159442043196543965989)
              ·
                refine ⟨15324404895383099351993623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81730159442043196543965989 15324404895383099351993623)
                ·
                  refine ⟨22986607343074649027990435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15324404895383099351993623 22986607343074649027990435)
                  ·
                    refine ⟨34479911014611973541985653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22986607343074649027990435 34479911014611973541985653)
                    ·
                      refine ⟨3232491657619872519561155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34479911014611973541985653 3232491657619872519561155)
                      ·
                        rfl

theorem cell23_6295255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_6295255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295255 prefixEnd_6295255 := by exact prefixLift 6295255
  have htrace : WordTrace (prefixWord ++ tailWord_6295255) baseStart_6295255 baseEnd_6295255 := by
    simpa [prefixWord, tailWord_6295255, baseEnd_6295255] using wordTrace_append hprefix tailTrace_6295255
  have hstable : (prefixWord ++ tailWord_6295255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295255).length < 2 ^ (prefixWord ++ tailWord_6295255).sum := by decide
  have hdescent : baseEnd_6295255 < baseStart_6295255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295269 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6295269 : Nat := 118140960795 + 6295269 * 2 ^ 59
def prefixEnd_6295269 : Nat := 4983230072969 + 3 ^ 40 * 6295269 * 2
def baseEnd_6295269 : Nat := 3232498846349035464786091

theorem tailTrace_6295269 : CollatzResearch.WordTrace tailWord_6295269 prefixEnd_6295269 3232498846349035464786091 := by
  unfold tailWord_6295269
  simp only [CollatzResearch.WordTrace]
  refine ⟨229607323430323034193536861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153071548953548689462357907 229607323430323034193536861)
  ·
    refine ⟨86102746286371137822576323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229607323430323034193536861 86102746286371137822576323)
    ·
      refine ⟨129154119429556706733864485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86102746286371137822576323 129154119429556706733864485)
      ·
        refine ⟨24216397393041882512599591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129154119429556706733864485 24216397393041882512599591)
        ·
          refine ⟨36324596089562823768899387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24216397393041882512599591 36324596089562823768899387)
          ·
            refine ⟨54486894134344235653349081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36324596089562823768899387 54486894134344235653349081)
            ·
              refine ⟨40865170600758176740011811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54486894134344235653349081 40865170600758176740011811)
              ·
                refine ⟨61297755901137265110017717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40865170600758176740011811 61297755901137265110017717)
                ·
                  refine ⟨5746664615731618604064161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61297755901137265110017717 5746664615731618604064161)
                  ·
                    refine ⟨4309998461798713953048121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5746664615731618604064161 4309998461798713953048121)
                    ·
                      refine ⟨3232498846349035464786091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4309998461798713953048121 3232498846349035464786091)
                      ·
                        rfl

theorem cell23_6295269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6295269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295269 prefixEnd_6295269 := by exact prefixLift 6295269
  have htrace : WordTrace (prefixWord ++ tailWord_6295269) baseStart_6295269 baseEnd_6295269 := by
    simpa [prefixWord, tailWord_6295269, baseEnd_6295269] using wordTrace_append hprefix tailTrace_6295269
  have hstable : (prefixWord ++ tailWord_6295269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295269).length < 2 ^ (prefixWord ++ tailWord_6295269).sum := by decide
  have hdescent : baseEnd_6295269 < baseStart_6295269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295282 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6295282 : Nat := 118140960795 + 6295282 * 2 ^ 59
def prefixEnd_6295282 : Nat := 4983230072969 + 3 ^ 40 * 6295282 * 2
def baseEnd_6295282 : Nat := 3232505521597543913923531

theorem tailTrace_6295282 : CollatzResearch.WordTrace tailWord_6295282 prefixEnd_6295282 3232505521597543913923531 := by
  unfold tailWord_6295282
  simp only [CollatzResearch.WordTrace]
  refine ⟨57401949394818984353440025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153071865052850624942506733 57401949394818984353440025)
  ·
    refine ⟨43051462046114238265080019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57401949394818984353440025 43051462046114238265080019)
    ·
      refine ⟨64577193069171357397620029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43051462046114238265080019 64577193069171357397620029)
      ·
        refine ⟨24216447400939259024107511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64577193069171357397620029 24216447400939259024107511)
        ·
          refine ⟨36324671101408888536161267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24216447400939259024107511 36324671101408888536161267)
          ·
            refine ⟨54487006652113332804241901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36324671101408888536161267 54487006652113332804241901)
            ·
              refine ⟨20432627494542499801590713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54487006652113332804241901 20432627494542499801590713)
              ·
                refine ⟨15324470620906874851193035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20432627494542499801590713 15324470620906874851193035)
                ·
                  refine ⟨22986705931360312276789553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15324470620906874851193035 22986705931360312276789553)
                  ·
                    refine ⟨17240029448520234207592165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22986705931360312276789553 17240029448520234207592165)
                    ·
                      refine ⟨3232505521597543913923531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17240029448520234207592165 3232505521597543913923531)
                      ·
                        rfl

theorem cell23_6295282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6295282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295282 prefixEnd_6295282 := by exact prefixLift 6295282
  have htrace : WordTrace (prefixWord ++ tailWord_6295282) baseStart_6295282 baseEnd_6295282 := by
    simpa [prefixWord, tailWord_6295282, baseEnd_6295282] using wordTrace_append hprefix tailTrace_6295282
  have hstable : (prefixWord ++ tailWord_6295282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295282).length < 2 ^ (prefixWord ++ tailWord_6295282).sum := by decide
  have hdescent : baseEnd_6295282 < baseStart_6295282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295286 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6295286 : Nat := 118140960795 + 6295286 * 2 ^ 59
def prefixEnd_6295286 : Nat := 4983230072969 + 3 ^ 40 * 6295286 * 2
def baseEnd_6295286 : Nat := 3232507575520161898273513

theorem tailTrace_6295286 : CollatzResearch.WordTrace tailWord_6295286 prefixEnd_6295286 3232507575520161898273513 := by
  unfold tailWord_6295286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14350496466953840381056607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153071962314174297397937141 14350496466953840381056607)
  ·
    refine ⟨21525744700430760571584911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14350496466953840381056607 21525744700430760571584911)
    ·
      refine ⟨32288617050646140857377367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21525744700430760571584911 32288617050646140857377367)
      ·
        refine ⟨48432925575969211286066051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32288617050646140857377367 48432925575969211286066051)
        ·
          refine ⟨72649388363953816929099077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48432925575969211286066051 72649388363953816929099077)
          ·
            refine ⟨13621760318241340674206077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72649388363953816929099077 13621760318241340674206077)
            ·
              refine ⟨5108160119340502752827279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13621760318241340674206077 5108160119340502752827279)
              ·
                refine ⟨7662240179010754129240919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108160119340502752827279 7662240179010754129240919)
                ·
                  refine ⟨11493360268516131193861379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662240179010754129240919 11493360268516131193861379)
                  ·
                    refine ⟨17240040402774196790792069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11493360268516131193861379 17240040402774196790792069)
                    ·
                      refine ⟨3232507575520161898273513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17240040402774196790792069 3232507575520161898273513)
                      ·
                        rfl

theorem cell23_6295286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6295286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295286 prefixEnd_6295286 := by exact prefixLift 6295286
  have htrace : WordTrace (prefixWord ++ tailWord_6295286) baseStart_6295286 baseEnd_6295286 := by
    simpa [prefixWord, tailWord_6295286, baseEnd_6295286] using wordTrace_append hprefix tailTrace_6295286
  have hstable : (prefixWord ++ tailWord_6295286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295286).length < 2 ^ (prefixWord ++ tailWord_6295286).sum := by decide
  have hdescent : baseEnd_6295286 < baseStart_6295286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295319 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_6295319 : Nat := 118140960795 + 6295319 * 2 ^ 59
def prefixEnd_6295319 : Nat := 4983230072969 + 3 ^ 40 * 6295319 * 2
def baseEnd_6295319 : Nat := 3232524520381760269160861

theorem tailTrace_6295319 : CollatzResearch.WordTrace tailWord_6295319 prefixEnd_6295319 3232524520381760269160861 := by
  unfold tailWord_6295319
  simp only [CollatzResearch.WordTrace]
  refine ⟨229609147080141892732857011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153072764720094595155238007 229609147080141892732857011)
  ·
    refine ⟨344413720620212839099285517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229609147080141892732857011 344413720620212839099285517)
    ·
      refine ⟨129155145232579814662232069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344413720620212839099285517 129155145232579814662232069)
      ·
        refine ⟨24216589731108715249168513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129155145232579814662232069 24216589731108715249168513)
        ·
          refine ⟨18162442298331536436876385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24216589731108715249168513 18162442298331536436876385)
          ·
            refine ⟨13621831723748652327657289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18162442298331536436876385 13621831723748652327657289)
            ·
              refine ⟨10216373792811489245742967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13621831723748652327657289 10216373792811489245742967)
              ·
                refine ⟨15324560689217233868614451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10216373792811489245742967 15324560689217233868614451)
                ·
                  refine ⟨22986841033825850802921677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15324560689217233868614451 22986841033825850802921677)
                  ·
                    refine ⟨8620065387684694051095629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22986841033825850802921677 8620065387684694051095629)
                    ·
                      refine ⟨3232524520381760269160861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8620065387684694051095629 3232524520381760269160861)
                      ·
                        rfl

theorem cell23_6295319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_6295319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295319 prefixEnd_6295319 := by exact prefixLift 6295319
  have htrace : WordTrace (prefixWord ++ tailWord_6295319) baseStart_6295319 baseEnd_6295319 := by
    simpa [prefixWord, tailWord_6295319, baseEnd_6295319] using wordTrace_append hprefix tailTrace_6295319
  have hstable : (prefixWord ++ tailWord_6295319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295319).length < 2 ^ (prefixWord ++ tailWord_6295319).sum := by decide
  have hdescent : baseEnd_6295319 < baseStart_6295319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295329 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_6295329 : Nat := 118140960795 + 6295329 * 2 ^ 59
def prefixEnd_6295329 : Nat := 4983230072969 + 3 ^ 40 * 6295329 * 2
def baseEnd_6295329 : Nat := 3232529655188305230035815

theorem tailTrace_6295329 : CollatzResearch.WordTrace tailWord_6295329 prefixEnd_6295329 3232529655188305230035815 := by
  unfold tailWord_6295329
  simp only [CollatzResearch.WordTrace]
  refine ⟨229609511810105664440721041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153073007873403776293814027 229609511810105664440721041)
  ·
    refine ⟨172207133857579248330540781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229609511810105664440721041 172207133857579248330540781)
    ·
      refine ⟨64577675196592218123952793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172207133857579248330540781 64577675196592218123952793)
      ·
        refine ⟨48433256397444163592964595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64577675196592218123952793 48433256397444163592964595)
        ·
          refine ⟨72649884596166245389446893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48433256397444163592964595 72649884596166245389446893)
          ·
            refine ⟨27243706723562342021042585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72649884596166245389446893 27243706723562342021042585)
            ·
              refine ⟨20432780042671756515781939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27243706723562342021042585 20432780042671756515781939)
              ·
                refine ⟨30649170064007634773672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20432780042671756515781939 30649170064007634773672909)
                ·
                  refine ⟨11493438774002863040127341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30649170064007634773672909 11493438774002863040127341)
                  ·
                    refine ⟨4310039540251073640047753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11493438774002863040127341 4310039540251073640047753)
                    ·
                      refine ⟨3232529655188305230035815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310039540251073640047753 3232529655188305230035815)
                      ·
                        rfl

theorem cell23_6295329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_6295329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295329 prefixEnd_6295329 := by exact prefixLift 6295329
  have htrace : WordTrace (prefixWord ++ tailWord_6295329) baseStart_6295329 baseEnd_6295329 := by
    simpa [prefixWord, tailWord_6295329, baseEnd_6295329] using wordTrace_append hprefix tailTrace_6295329
  have hstable : (prefixWord ++ tailWord_6295329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295329).length < 2 ^ (prefixWord ++ tailWord_6295329).sum := by decide
  have hdescent : baseEnd_6295329 < baseStart_6295329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295346 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_6295346 : Nat := 118140960795 + 6295346 * 2 ^ 59
def prefixEnd_6295346 : Nat := 4983230072969 + 3 ^ 40 * 6295346 * 2
def baseEnd_6295346 : Nat := 3232538384359431663523237

theorem tailTrace_6295346 : CollatzResearch.WordTrace tailWord_6295346 prefixEnd_6295346 3232538384359431663523237 := by
  unfold tailWord_6295346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57402532962761019086022473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153073421234029384229393261 57402532962761019086022473)
  ·
    refine ⟨43051899722070764314516855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57402532962761019086022473 43051899722070764314516855)
    ·
      refine ⟨64577849583106146471775283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43051899722070764314516855 64577849583106146471775283)
      ·
        refine ⟨96866774374659219707662925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64577849583106146471775283 96866774374659219707662925)
        ·
          refine ⟨36325040390497207390373597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96866774374659219707662925 36325040390497207390373597)
          ·
            refine ⟨13621890146436452771390099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36325040390497207390373597 13621890146436452771390099)
            ·
              refine ⟨20432835219654679157085149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13621890146436452771390099 20432835219654679157085149)
              ·
                refine ⟨7662313207370504683906931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20432835219654679157085149 7662313207370504683906931)
                ·
                  refine ⟨11493469811055757025860397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662313207370504683906931 11493469811055757025860397)
                  ·
                    refine ⟨4310051179145908884697649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11493469811055757025860397 4310051179145908884697649)
                    ·
                      refine ⟨3232538384359431663523237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310051179145908884697649 3232538384359431663523237)
                      ·
                        rfl

theorem cell23_6295346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_6295346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295346 prefixEnd_6295346 := by exact prefixLift 6295346
  have htrace : WordTrace (prefixWord ++ tailWord_6295346) baseStart_6295346 baseEnd_6295346 := by
    simpa [prefixWord, tailWord_6295346, baseEnd_6295346] using wordTrace_append hprefix tailTrace_6295346
  have hstable : (prefixWord ++ tailWord_6295346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295346).length < 2 ^ (prefixWord ++ tailWord_6295346).sum := by decide
  have hdescent : baseEnd_6295346 < baseStart_6295346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295415 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_6295415 : Nat := 118140960795 + 6295415 * 2 ^ 59
def prefixEnd_6295415 : Nat := 4983230072969 + 3 ^ 40 * 6295415 * 2
def baseEnd_6295415 : Nat := 3232573814524591893560419

theorem tailTrace_6295415 : CollatzResearch.WordTrace tailWord_6295415 prefixEnd_6295415 3232573814524591893560419 := by
  unfold tailWord_6295415
  simp only [CollatzResearch.WordTrace]
  refine ⟨229612648487794101128351699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153075098991862734085567799 229612648487794101128351699)
  ·
    refine ⟨344418972731691151692527549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229612648487794101128351699 344418972731691151692527549)
    ·
      refine ⟨129157114774384181884697831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344418972731691151692527549 129157114774384181884697831)
      ·
        refine ⟨193735672161576272827046747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129157114774384181884697831 193735672161576272827046747)
        ·
          refine ⟨290603508242364409240570121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193735672161576272827046747 290603508242364409240570121)
          ·
            refine ⟨217952631181773306930427591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290603508242364409240570121 217952631181773306930427591)
            ·
              refine ⟨326928946772659960395641387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217952631181773306930427591 326928946772659960395641387)
              ·
                refine ⟨490393420158989940593462081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326928946772659960395641387 490393420158989940593462081)
                ·
                  refine ⟨367795065119242455445096561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490393420158989940593462081 367795065119242455445096561)
                  ·
                    refine ⟨275846298839431841583822421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 367795065119242455445096561 275846298839431841583822421)
                    ·
                      refine ⟨3232573814524591893560419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275846298839431841583822421 3232573814524591893560419)
                      ·
                        rfl

theorem cell23_6295415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_6295415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295415 prefixEnd_6295415 := by exact prefixLift 6295415
  have htrace : WordTrace (prefixWord ++ tailWord_6295415) baseStart_6295415 baseEnd_6295415 := by
    simpa [prefixWord, tailWord_6295415, baseEnd_6295415] using wordTrace_append hprefix tailTrace_6295415
  have hstable : (prefixWord ++ tailWord_6295415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295415).length < 2 ^ (prefixWord ++ tailWord_6295415).sum := by decide
  have hdescent : baseEnd_6295415 < baseStart_6295415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295532 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_6295532 : Nat := 118140960795 + 6295532 * 2 ^ 59
def prefixEnd_6295532 : Nat := 4983230072969 + 3 ^ 40 * 6295532 * 2
def baseEnd_6295532 : Nat := 1077544630587055978599127

theorem tailTrace_6295532 : CollatzResearch.WordTrace tailWord_6295532 prefixEnd_6295532 1077544630587055978599127 := by
  unfold tailWord_6295532
  simp only [CollatzResearch.WordTrace]
  refine ⟨114808457914185115055180425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153077943885580153406907233 114808457914185115055180425)
  ·
    refine ⟨86106343435638836291385319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114808457914185115055180425 86106343435638836291385319)
    ·
      refine ⟨129159515153458254437077979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86106343435638836291385319 129159515153458254437077979)
      ·
        refine ⟨193739272730187381655616969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129159515153458254437077979 193739272730187381655616969)
        ·
          refine ⟨145304454547640536241712727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193739272730187381655616969 145304454547640536241712727)
          ·
            refine ⟨217956681821460804362569091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145304454547640536241712727 217956681821460804362569091)
            ·
              refine ⟨326935022732191206543853637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217956681821460804362569091 326935022732191206543853637)
              ·
                refine ⟨61300316762285851226972557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326935022732191206543853637 61300316762285851226972557)
                ·
                  refine ⟨22987618785857194210114709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61300316762285851226972557 22987618785857194210114709)
                  ·
                    refine ⟨1077544630587055978599127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22987618785857194210114709 1077544630587055978599127)
                    ·
                      rfl

theorem cell23_6295532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_6295532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295532 prefixEnd_6295532 := by exact prefixLift 6295532
  have htrace : WordTrace (prefixWord ++ tailWord_6295532) baseStart_6295532 baseEnd_6295532 := by
    simpa [prefixWord, tailWord_6295532, baseEnd_6295532] using wordTrace_append hprefix tailTrace_6295532
  have hstable : (prefixWord ++ tailWord_6295532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295532).length < 2 ^ (prefixWord ++ tailWord_6295532).sum := by decide
  have hdescent : baseEnd_6295532 < baseStart_6295532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295549 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_6295549 : Nat := 118140960795 + 6295549 * 2 ^ 59
def prefixEnd_6295549 : Nat := 4983230072969 + 3 ^ 40 * 6295549 * 2
def baseEnd_6295549 : Nat := 1077547540310764789761601

theorem tailTrace_6295549 : CollatzResearch.WordTrace tailWord_6295549 prefixEnd_6295549 1077547540310764789761601 := by
  unfold tailWord_6295549
  simp only [CollatzResearch.WordTrace]
  refine ⟨229617535869308642013729701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153078357246205761342486467 229617535869308642013729701)
  ·
    refine ⟨43053287975495370377574319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229617535869308642013729701 43053287975495370377574319)
    ·
      refine ⟨64579931963243055566361479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43053287975495370377574319 64579931963243055566361479)
      ·
        refine ⟨96869897944864583349542219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64579931963243055566361479 96869897944864583349542219)
        ·
          refine ⟨145304846917296875024313329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96869897944864583349542219 145304846917296875024313329)
          ·
            refine ⟨108978635187972656268234997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145304846917296875024313329 108978635187972656268234997)
            ·
              refine ⟨10216747048872436525147031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108978635187972656268234997 10216747048872436525147031)
              ·
                refine ⟨15325120573308654787720547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10216747048872436525147031 15325120573308654787720547)
                ·
                  refine ⟨22987680859962982181580821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15325120573308654787720547 22987680859962982181580821)
                  ·
                    refine ⟨1077547540310764789761601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22987680859962982181580821 1077547540310764789761601)
                    ·
                      rfl

theorem cell23_6295549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_6295549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295549 prefixEnd_6295549 := by exact prefixLift 6295549
  have htrace : WordTrace (prefixWord ++ tailWord_6295549) baseStart_6295549 baseEnd_6295549 := by
    simpa [prefixWord, tailWord_6295549, baseEnd_6295549] using wordTrace_append hprefix tailTrace_6295549
  have hstable : (prefixWord ++ tailWord_6295549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295549).length < 2 ^ (prefixWord ++ tailWord_6295549).sum := by decide
  have hdescent : baseEnd_6295549 < baseStart_6295549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295576 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6295576 : Nat := 118140960795 + 6295576 * 2 ^ 59
def prefixEnd_6295576 : Nat := 4983230072969 + 3 ^ 40 * 6295576 * 2
def baseEnd_6295576 : Nat := 3232656484909965763647179

theorem tailTrace_6295576 : CollatzResearch.WordTrace tailWord_6295576 prefixEnd_6295576 3232656484909965763647179 := by
  unfold tailWord_6295576
  simp only [CollatzResearch.WordTrace]
  refine ⟨114809260320105412812481291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153079013760140550416641721 114809260320105412812481291)
  ·
    refine ⟨172213890480158119218721937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114809260320105412812481291 172213890480158119218721937)
    ·
      refine ⟨129160417860118589414041453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172213890480158119218721937 129160417860118589414041453)
      ·
        refine ⟨48435156697544471030265545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129160417860118589414041453 48435156697544471030265545)
        ·
          refine ⟨36326367523158353272699159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48435156697544471030265545 36326367523158353272699159)
          ·
            refine ⟨54489551284737529909048739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36326367523158353272699159 54489551284737529909048739)
            ·
              refine ⟨81734326927106294863573109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54489551284737529909048739 81734326927106294863573109)
              ·
                refine ⟨7662593149416215143459979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81734326927106294863573109 7662593149416215143459979)
                ·
                  refine ⟨11493889724124322715189969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662593149416215143459979 11493889724124322715189969)
                  ·
                    refine ⟨8620417293093242036392477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11493889724124322715189969 8620417293093242036392477)
                    ·
                      refine ⟨3232656484909965763647179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8620417293093242036392477 3232656484909965763647179)
                      ·
                        rfl

theorem cell23_6295576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6295576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295576 prefixEnd_6295576 := by exact prefixLift 6295576
  have htrace : WordTrace (prefixWord ++ tailWord_6295576) baseStart_6295576 baseEnd_6295576 := by
    simpa [prefixWord, tailWord_6295576, baseEnd_6295576] using wordTrace_append hprefix tailTrace_6295576
  have hstable : (prefixWord ++ tailWord_6295576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295576).length < 2 ^ (prefixWord ++ tailWord_6295576).sum := by decide
  have hdescent : baseEnd_6295576 < baseStart_6295576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295663 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 1, 4, 2]
def baseStart_6295663 : Nat := 118140960795 + 6295663 * 2 ^ 59
def prefixEnd_6295663 : Nat := 4983230072969 + 3 ^ 40 * 6295663 * 2
def baseEnd_6295663 : Nat := 3232701157726906923259279

theorem tailTrace_6295663 : CollatzResearch.WordTrace tailWord_6295663 prefixEnd_6295663 3232701157726906923259279 := by
  unfold tailWord_6295663
  simp only [CollatzResearch.WordTrace]
  refine ⟨229621693790895639483379643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153081129193930426322253095 229621693790895639483379643)
  ·
    refine ⟨344432540686343459225069465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229621693790895639483379643 344432540686343459225069465)
    ·
      refine ⟨258324405514757594418802099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344432540686343459225069465 258324405514757594418802099)
      ·
        refine ⟨387486608272136391628203149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258324405514757594418802099 387486608272136391628203149)
        ·
          refine ⟨145307478102051146860576181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387486608272136391628203149 145307478102051146860576181)
          ·
            refine ⟨13622576072067295018179017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145307478102051146860576181 13622576072067295018179017)
            ·
              refine ⟨10216932054050471263634263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13622576072067295018179017 10216932054050471263634263)
              ·
                refine ⟨15325398081075706895451395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10216932054050471263634263 15325398081075706895451395)
                ·
                  refine ⟨22988097121613560343177093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15325398081075706895451395 22988097121613560343177093)
                  ·
                    refine ⟨4310268210302542564345705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22988097121613560343177093 4310268210302542564345705)
                    ·
                      refine ⟨3232701157726906923259279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310268210302542564345705 3232701157726906923259279)
                      ·
                        rfl

theorem cell23_6295663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4, 2].length) (baseStart_6295663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295663 prefixEnd_6295663 := by exact prefixLift 6295663
  have htrace : WordTrace (prefixWord ++ tailWord_6295663) baseStart_6295663 baseEnd_6295663 := by
    simpa [prefixWord, tailWord_6295663, baseEnd_6295663] using wordTrace_append hprefix tailTrace_6295663
  have hstable : (prefixWord ++ tailWord_6295663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295663).length < 2 ^ (prefixWord ++ tailWord_6295663).sum := by decide
  have hdescent : baseEnd_6295663 < baseStart_6295663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295699 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 4, 5]
def baseStart_6295699 : Nat := 118140960795 + 6295699 * 2 ^ 59
def prefixEnd_6295699 : Nat := 4983230072969 + 3 ^ 40 * 6295699 * 2
def baseEnd_6295699 : Nat := 1077573214343489594136371

theorem tailTrace_6295699 : CollatzResearch.WordTrace tailWord_6295699 prefixEnd_6295699 1077573214343489594136371 := by
  unfold tailWord_6295699
  simp only [CollatzResearch.WordTrace]
  refine ⟨229623006818765217631690151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153082004545843478421126767 229623006818765217631690151)
  ·
    refine ⟨344434510228147826447535227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229623006818765217631690151 344434510228147826447535227)
    ·
      refine ⟨516651765342221739671302841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344434510228147826447535227 516651765342221739671302841)
      ·
        refine ⟨387488824006666304753477131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516651765342221739671302841 387488824006666304753477131)
        ·
          refine ⟨581233236009999457130215697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387488824006666304753477131 581233236009999457130215697)
          ·
            refine ⟨435924927007499592847661773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581233236009999457130215697 435924927007499592847661773)
            ·
              refine ⟨163471847627812347317873165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435924927007499592847661773 163471847627812347317873165)
              ·
                refine ⟨61301942860429630244202437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163471847627812347317873165 61301942860429630244202437)
                ·
                  refine ⟨11494114286330555670787957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61301942860429630244202437 11494114286330555670787957)
                  ·
                    refine ⟨1077573214343489594136371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11494114286330555670787957 1077573214343489594136371)
                    ·
                      rfl

theorem cell23_6295699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 5].length) (baseStart_6295699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295699 prefixEnd_6295699 := by exact prefixLift 6295699
  have htrace : WordTrace (prefixWord ++ tailWord_6295699) baseStart_6295699 baseEnd_6295699 := by
    simpa [prefixWord, tailWord_6295699, baseEnd_6295699] using wordTrace_append hprefix tailTrace_6295699
  have hstable : (prefixWord ++ tailWord_6295699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295699).length < 2 ^ (prefixWord ++ tailWord_6295699).sum := by decide
  have hdescent : baseEnd_6295699 < baseStart_6295699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295714 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6295714 : Nat := 118140960795 + 6295714 * 2 ^ 59
def prefixEnd_6295714 : Nat := 4983230072969 + 3 ^ 40 * 6295714 * 2
def baseEnd_6295714 : Nat := 3232727345240286223721545

theorem tailTrace_6295714 : CollatzResearch.WordTrace tailWord_6295714 prefixEnd_6295714 3232727345240286223721545 := by
  unfold tailWord_6295714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57405888478427718798371549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153082369275807250128990797 57405888478427718798371549)
  ·
    refine ⟨21527208179410394549389331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57405888478427718798371549 21527208179410394549389331)
    ·
      refine ⟨32290812269115591824083997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527208179410394549389331 32290812269115591824083997)
      ·
        refine ⟨12109054600918346934031499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32290812269115591824083997 12109054600918346934031499)
        ·
          refine ⟨18163581901377520401047249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12109054600918346934031499 18163581901377520401047249)
          ·
            refine ⟨13622686426033140300785437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18163581901377520401047249 13622686426033140300785437)
            ·
              refine ⟨5108507409762427612794539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13622686426033140300785437 5108507409762427612794539)
              ·
                refine ⟨7662761114643641419191809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108507409762427612794539 7662761114643641419191809)
                ·
                  refine ⟨5747070835982731064393857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7662761114643641419191809 5747070835982731064393857)
                  ·
                    refine ⟨4310303126987048298295393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5747070835982731064393857 4310303126987048298295393)
                    ·
                      refine ⟨3232727345240286223721545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310303126987048298295393 3232727345240286223721545)
                      ·
                        rfl

theorem cell23_6295714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6295714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295714 prefixEnd_6295714 := by exact prefixLift 6295714
  have htrace : WordTrace (prefixWord ++ tailWord_6295714) baseStart_6295714 baseEnd_6295714 := by
    simpa [prefixWord, tailWord_6295714, baseEnd_6295714] using wordTrace_append hprefix tailTrace_6295714
  have hstable : (prefixWord ++ tailWord_6295714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295714).length < 2 ^ (prefixWord ++ tailWord_6295714).sum := by decide
  have hdescent : baseEnd_6295714 < baseStart_6295714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295736 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_6295736 : Nat := 118140960795 + 6295736 * 2 ^ 59
def prefixEnd_6295736 : Nat := 4983230072969 + 3 ^ 40 * 6295736 * 2
def baseEnd_6295736 : Nat := 3232738641814685137646443

theorem tailTrace_6295736 : CollatzResearch.WordTrace tailWord_6295736 prefixEnd_6295736 3232738641814685137646443 := by
  unfold tailWord_6295736
  simp only [CollatzResearch.WordTrace]
  refine ⟨114812178159815586475393531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153082904213087448633858041 114812178159815586475393531)
  ·
    refine ⟨172218267239723379713090297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114812178159815586475393531 172218267239723379713090297)
    ·
      refine ⟨129163700429792534784817723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172218267239723379713090297 129163700429792534784817723)
      ·
        refine ⟨193745550644688802177226585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129163700429792534784817723 193745550644688802177226585)
        ·
          refine ⟨145309162983516601632919939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193745550644688802177226585 145309162983516601632919939)
          ·
            refine ⟨217963744475274902449379909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145309162983516601632919939 217963744475274902449379909)
            ·
              refine ⟨40868202089114044209258733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217963744475274902449379909 40868202089114044209258733)
              ·
                refine ⟨15325575783417766578472025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40868202089114044209258733 15325575783417766578472025)
                ·
                  refine ⟨11494181837563324933854019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15325575783417766578472025 11494181837563324933854019)
                  ·
                    refine ⟨17241272756344987400781029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11494181837563324933854019 17241272756344987400781029)
                    ·
                      refine ⟨3232738641814685137646443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17241272756344987400781029 3232738641814685137646443)
                      ·
                        rfl

theorem cell23_6295736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_6295736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295736 prefixEnd_6295736 := by exact prefixLift 6295736
  have htrace : WordTrace (prefixWord ++ tailWord_6295736) baseStart_6295736 baseEnd_6295736 := by
    simpa [prefixWord, tailWord_6295736, baseEnd_6295736] using wordTrace_append hprefix tailTrace_6295736
  have hstable : (prefixWord ++ tailWord_6295736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295736).length < 2 ^ (prefixWord ++ tailWord_6295736).sum := by decide
  have hdescent : baseEnd_6295736 < baseStart_6295736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295749 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_6295749 : Nat := 118140960795 + 6295749 * 2 ^ 59
def prefixEnd_6295749 : Nat := 4983230072969 + 3 ^ 40 * 6295749 * 2
def baseEnd_6295749 : Nat := 3232745317063193586783883

theorem tailTrace_6295749 : CollatzResearch.WordTrace tailWord_6295749 prefixEnd_6295749 3232745317063193586783883 := by
  unfold tailWord_6295749
  simp only [CollatzResearch.WordTrace]
  refine ⟨229624830468584076171010301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153083220312389384114006867 229624830468584076171010301)
  ·
    refine ⟨86109311425719028564128863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229624830468584076171010301 86109311425719028564128863)
    ·
      refine ⟨129163967138578542846193295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86109311425719028564128863 129163967138578542846193295)
      ·
        refine ⟨193745950707867814269289943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129163967138578542846193295 193745950707867814269289943)
        ·
          refine ⟨290618926061801721403934915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193745950707867814269289943 290618926061801721403934915)
          ·
            refine ⟨435928389092702582105902373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290618926061801721403934915 435928389092702582105902373)
            ·
              refine ⟨81736572954881734144856695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 435928389092702582105902373 81736572954881734144856695)
              ·
                refine ⟨122604859432322601217285043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81736572954881734144856695 122604859432322601217285043)
                ·
                  refine ⟨183907289148483901825927565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122604859432322601217285043 183907289148483901825927565)
                  ·
                    refine ⟨68965233430681463184722837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183907289148483901825927565 68965233430681463184722837)
                    ·
                      refine ⟨3232745317063193586783883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68965233430681463184722837 3232745317063193586783883)
                      ·
                        rfl

theorem cell23_6295749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_6295749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295749 prefixEnd_6295749 := by exact prefixLift 6295749
  have htrace : WordTrace (prefixWord ++ tailWord_6295749) baseStart_6295749 baseEnd_6295749 := by
    simpa [prefixWord, tailWord_6295749, baseEnd_6295749] using wordTrace_append hprefix tailTrace_6295749
  have hstable : (prefixWord ++ tailWord_6295749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295749).length < 2 ^ (prefixWord ++ tailWord_6295749).sum := by decide
  have hdescent : baseEnd_6295749 < baseStart_6295749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295759 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 8]
def baseStart_6295759 : Nat := 118140960795 + 6295759 * 2 ^ 59
def prefixEnd_6295759 : Nat := 4983230072969 + 3 ^ 40 * 6295759 * 2
def baseEnd_6295759 : Nat := 359194494652193171962093

theorem tailTrace_6295759 : CollatzResearch.WordTrace tailWord_6295759 prefixEnd_6295759 359194494652193171962093 := by
  unfold tailWord_6295759
  simp only [CollatzResearch.WordTrace]
  refine ⟨229625195198547847878874331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153083463465698565252582887 229625195198547847878874331)
  ·
    refine ⟨344437792797821771818311497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229625195198547847878874331 344437792797821771818311497)
    ·
      refine ⟨258328344598366328863733623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344437792797821771818311497 258328344598366328863733623)
      ·
        refine ⟨387492516897549493295600435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258328344598366328863733623 387492516897549493295600435)
        ·
          refine ⟨581238775346324239943400653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387492516897549493295600435 581238775346324239943400653)
          ·
            refine ⟨217964540754871589978775245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581238775346324239943400653 217964540754871589978775245)
            ·
              refine ⟨81736702783076846242040717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217964540754871589978775245 81736702783076846242040717)
              ·
                refine ⟨30651263543653817340765269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81736702783076846242040717 30651263543653817340765269)
                ·
                  refine ⟨359194494652193171962093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30651263543653817340765269 359194494652193171962093)
                  ·
                    rfl

theorem cell23_6295759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 8].length) (baseStart_6295759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295759 prefixEnd_6295759 := by exact prefixLift 6295759
  have htrace : WordTrace (prefixWord ++ tailWord_6295759) baseStart_6295759 baseEnd_6295759 := by
    simpa [prefixWord, tailWord_6295759, baseEnd_6295759] using wordTrace_append hprefix tailTrace_6295759
  have hstable : (prefixWord ++ tailWord_6295759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295759).length < 2 ^ (prefixWord ++ tailWord_6295759).sum := by decide
  have hdescent : baseEnd_6295759 < baseStart_6295759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295776 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 6]
def baseStart_6295776 : Nat := 118140960795 + 6295776 * 2 ^ 59
def prefixEnd_6295776 : Nat := 4983230072969 + 3 ^ 40 * 6295776 * 2
def baseEnd_6295776 : Nat := 359195464560096109016251

theorem tailTrace_6295776 : CollatzResearch.WordTrace tailWord_6295776 prefixEnd_6295776 359195464560096109016251 := by
  unfold tailWord_6295776
  simp only [CollatzResearch.WordTrace]
  refine ⟨114812907619743129891121591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153083876826324173188162121 114812907619743129891121591)
  ·
    refine ⟨172219361429614694836682387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114812907619743129891121591 172219361429614694836682387)
    ·
      refine ⟨258329042144422042255023581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172219361429614694836682387 258329042144422042255023581)
      ·
        refine ⟨96873390804158265845633843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258329042144422042255023581 96873390804158265845633843)
        ·
          refine ⟨145310086206237398768450765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96873390804158265845633843 145310086206237398768450765)
          ·
            refine ⟨54491282327339024538169037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145310086206237398768450765 54491282327339024538169037)
            ·
              refine ⟨20434230872752134201813389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54491282327339024538169037 20434230872752134201813389)
              ·
                refine ⟨7662836577282050325680021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20434230872752134201813389 7662836577282050325680021)
                ·
                  refine ⟨359195464560096109016251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7662836577282050325680021 359195464560096109016251)
                  ·
                    rfl

theorem cell23_6295776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_6295776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295776 prefixEnd_6295776 := by exact prefixLift 6295776
  have htrace : WordTrace (prefixWord ++ tailWord_6295776) baseStart_6295776 baseEnd_6295776 := by
    simpa [prefixWord, tailWord_6295776, baseEnd_6295776] using wordTrace_append hprefix tailTrace_6295776
  have hstable : (prefixWord ++ tailWord_6295776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295776).length < 2 ^ (prefixWord ++ tailWord_6295776).sum := by decide
  have hdescent : baseEnd_6295776 < baseStart_6295776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295810 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6295810 : Nat := 118140960795 + 6295810 * 2 ^ 59
def prefixEnd_6295810 : Nat := 4983230072969 + 3 ^ 40 * 6295810 * 2
def baseEnd_6295810 : Nat := 359197404375901983124567

theorem tailTrace_6295810 : CollatzResearch.WordTrace tailWord_6295810 prefixEnd_6295810 359197404375901983124567 := by
  unfold tailWord_6295810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57406763830340770897245221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153084703547575389059320589 57406763830340770897245221)
  ·
    refine ⟨10763768218188894543233479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57406763830340770897245221 10763768218188894543233479)
    ·
      refine ⟨16145652327283341814850219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10763768218188894543233479 16145652327283341814850219)
      ·
        refine ⟨24218478490925012722275329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16145652327283341814850219 24218478490925012722275329)
        ·
          refine ⟨18163858868193759541706497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24218478490925012722275329 18163858868193759541706497)
          ·
            refine ⟨13622894151145319656279873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18163858868193759541706497 13622894151145319656279873)
            ·
              refine ⟨10217170613358989742209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13622894151145319656279873 10217170613358989742209905)
              ·
                refine ⟨7662877960019242306657429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10217170613358989742209905 7662877960019242306657429)
                ·
                  refine ⟨359197404375901983124567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7662877960019242306657429 359197404375901983124567)
                  ·
                    rfl

theorem cell23_6295810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6295810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295810 prefixEnd_6295810 := by exact prefixLift 6295810
  have htrace : WordTrace (prefixWord ++ tailWord_6295810) baseStart_6295810 baseEnd_6295810 := by
    simpa [prefixWord, tailWord_6295810, baseEnd_6295810] using wordTrace_append hprefix tailTrace_6295810
  have hstable : (prefixWord ++ tailWord_6295810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295810).length < 2 ^ (prefixWord ++ tailWord_6295810).sum := by decide
  have hdescent : baseEnd_6295810 < baseStart_6295810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295813 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_6295813 : Nat := 118140960795 + 6295813 * 2 ^ 59
def prefixEnd_6295813 : Nat := 4983230072969 + 3 ^ 40 * 6295813 * 2
def baseEnd_6295813 : Nat := 3232778179825081336383589

theorem tailTrace_6295813 : CollatzResearch.WordTrace tailWord_6295813 prefixEnd_6295813 3232778179825081336383589 := by
  unfold tailWord_6295813
  simp only [CollatzResearch.WordTrace]
  refine ⟨229627164740352215101340093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153084776493568143400893395 229627164740352215101340093)
  ·
    refine ⟨86110186777632080663002535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229627164740352215101340093 86110186777632080663002535)
    ·
      refine ⟨129165280166448120994503803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86110186777632080663002535 129165280166448120994503803)
      ·
        refine ⟨193747920249672181491755705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129165280166448120994503803 193747920249672181491755705)
        ·
          refine ⟨145310940187254136118816779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193747920249672181491755705 145310940187254136118816779)
          ·
            refine ⟨217966410280881204178225169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145310940187254136118816779 217966410280881204178225169)
            ·
              refine ⟨163474807710660903133668877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217966410280881204178225169 163474807710660903133668877)
              ·
                refine ⟨61303052891497838675125829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163474807710660903133668877 61303052891497838675125829)
                ·
                  refine ⟨11494322417155844751586093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61303052891497838675125829 11494322417155844751586093)
                  ·
                    refine ⟨4310370906433441781844785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11494322417155844751586093 4310370906433441781844785)
                    ·
                      refine ⟨3232778179825081336383589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310370906433441781844785 3232778179825081336383589)
                      ·
                        rfl

theorem cell23_6295813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_6295813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295813 prefixEnd_6295813 := by exact prefixLift 6295813
  have htrace : WordTrace (prefixWord ++ tailWord_6295813) baseStart_6295813 baseEnd_6295813 := by
    simpa [prefixWord, tailWord_6295813, baseEnd_6295813] using wordTrace_append hprefix tailTrace_6295813
  have hstable : (prefixWord ++ tailWord_6295813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295813).length < 2 ^ (prefixWord ++ tailWord_6295813).sum := by decide
  have hdescent : baseEnd_6295813 < baseStart_6295813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295837 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6295837 : Nat := 118140960795 + 6295837 * 2 ^ 59
def prefixEnd_6295837 : Nat := 4983230072969 + 3 ^ 40 * 6295837 * 2
def baseEnd_6295837 : Nat := 3232790503360789242483479

theorem tailTrace_6295837 : CollatzResearch.WordTrace tailWord_6295837 prefixEnd_6295837 3232790503360789242483479 := by
  unfold tailWord_6295837
  simp only [CollatzResearch.WordTrace]
  refine ⟨229628040092265267200213765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153085360061510178133475843 229628040092265267200213765)
  ·
    refine ⟨43055257517299737600040081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229628040092265267200213765 43055257517299737600040081)
    ·
      refine ⟨32291443137974803200030061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43055257517299737600040081 32291443137974803200030061)
      ·
        refine ⟨12109291176740551200011273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32291443137974803200030061 12109291176740551200011273)
        ·
          refine ⟨9081968382555413400008455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12109291176740551200011273 9081968382555413400008455)
          ·
            refine ⟨13622952573833120100012683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9081968382555413400008455 13622952573833120100012683)
            ·
              refine ⟨20434428860749680150019025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13622952573833120100012683 20434428860749680150019025)
              ·
                refine ⟨15325821645562260112514269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20434428860749680150019025 15325821645562260112514269)
                ·
                  refine ⟨5747183117085847542192851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15325821645562260112514269 5747183117085847542192851)
                  ·
                    refine ⟨8620774675628771313289277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5747183117085847542192851 8620774675628771313289277)
                    ·
                      refine ⟨3232790503360789242483479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8620774675628771313289277 3232790503360789242483479)
                      ·
                        rfl

theorem cell23_6295837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6295837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295837 prefixEnd_6295837 := by exact prefixLift 6295837
  have htrace : WordTrace (prefixWord ++ tailWord_6295837) baseStart_6295837 baseEnd_6295837 := by
    simpa [prefixWord, tailWord_6295837, baseEnd_6295837] using wordTrace_append hprefix tailTrace_6295837
  have hstable : (prefixWord ++ tailWord_6295837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295837).length < 2 ^ (prefixWord ++ tailWord_6295837).sum := by decide
  have hdescent : baseEnd_6295837 < baseStart_6295837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295843 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 4]
def baseStart_6295843 : Nat := 118140960795 + 6295843 * 2 ^ 59
def prefixEnd_6295843 : Nat := 4983230072969 + 3 ^ 40 * 6295843 * 2
def baseEnd_6295843 : Nat := 3232793584244716219008451

theorem tailTrace_6295843 : CollatzResearch.WordTrace tailWord_6295843 prefixEnd_6295843 3232793584244716219008451 := by
  unfold tailWord_6295843
  simp only [CollatzResearch.WordTrace]
  refine ⟨229628258930243530224932183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153085505953495686816621455 229628258930243530224932183)
  ·
    refine ⟨344442388395365295337398275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229628258930243530224932183 344442388395365295337398275)
    ·
      refine ⟨516663582593047943006097413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344442388395365295337398275 516663582593047943006097413)
      ·
        refine ⟨96874421736196489313643265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516663582593047943006097413 96874421736196489313643265)
        ·
          refine ⟨72655816302147366985232449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96874421736196489313643265 72655816302147366985232449)
          ·
            refine ⟨54491862226610525238924337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72655816302147366985232449 54491862226610525238924337)
            ·
              refine ⟨40868896669957893929193253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54491862226610525238924337 40868896669957893929193253)
              ·
                refine ⟨7662918125617105111723735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40868896669957893929193253 7662918125617105111723735)
                ·
                  refine ⟨11494377188425657667585603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662918125617105111723735 11494377188425657667585603)
                  ·
                    refine ⟨17241565782638486501378405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11494377188425657667585603 17241565782638486501378405)
                    ·
                      refine ⟨3232793584244716219008451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17241565782638486501378405 3232793584244716219008451)
                      ·
                        rfl

theorem cell23_6295843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_6295843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295843 prefixEnd_6295843 := by exact prefixLift 6295843
  have htrace : WordTrace (prefixWord ++ tailWord_6295843) baseStart_6295843 baseEnd_6295843 := by
    simpa [prefixWord, tailWord_6295843, baseEnd_6295843] using wordTrace_append hprefix tailTrace_6295843
  have hstable : (prefixWord ++ tailWord_6295843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295843).length < 2 ^ (prefixWord ++ tailWord_6295843).sum := by decide
  have hdescent : baseEnd_6295843 < baseStart_6295843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295856 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_6295856 : Nat := 118140960795 + 6295856 * 2 ^ 59
def prefixEnd_6295856 : Nat := 4983230072969 + 3 ^ 40 * 6295856 * 2
def baseEnd_6295856 : Nat := 3232800259493224668145891

theorem tailTrace_6295856 : CollatzResearch.WordTrace tailWord_6295856 prefixEnd_6295856 3232800259493224668145891 := by
  unfold tailWord_6295856
  simp only [CollatzResearch.WordTrace]
  refine ⟨114814366539598216722577711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153085822052797622296770281 114814366539598216722577711)
  ·
    refine ⟨172221549809397325083866567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114814366539598216722577711 172221549809397325083866567)
    ·
      refine ⟨258332324714095987625799851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172221549809397325083866567 258332324714095987625799851)
      ·
        refine ⟨387498487071143981438699777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258332324714095987625799851 387498487071143981438699777)
        ·
          refine ⟨290623865303357986079024833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387498487071143981438699777 290623865303357986079024833)
          ·
            refine ⟨217967898977518489559268625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290623865303357986079024833 217967898977518489559268625)
            ·
              refine ⟨163475924233138867169451469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217967898977518489559268625 163475924233138867169451469)
              ·
                refine ⟨61303471587427075188544301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163475924233138867169451469 61303471587427075188544301)
                ·
                  refine ⟨22988801845285153195704113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61303471587427075188544301 22988801845285153195704113)
                  ·
                    refine ⟨17241601383963864896778085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22988801845285153195704113 17241601383963864896778085)
                    ·
                      refine ⟨3232800259493224668145891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17241601383963864896778085 3232800259493224668145891)
                      ·
                        rfl

theorem cell23_6295856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_6295856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295856 prefixEnd_6295856 := by exact prefixLift 6295856
  have htrace : WordTrace (prefixWord ++ tailWord_6295856) baseStart_6295856 baseEnd_6295856 := by
    simpa [prefixWord, tailWord_6295856, baseEnd_6295856] using wordTrace_append hprefix tailTrace_6295856
  have hstable : (prefixWord ++ tailWord_6295856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295856).length < 2 ^ (prefixWord ++ tailWord_6295856).sum := by decide
  have hdescent : baseEnd_6295856 < baseStart_6295856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295857 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 1, 5]
def baseStart_6295857 : Nat := 118140960795 + 6295857 * 2 ^ 59
def prefixEnd_6295857 : Nat := 4983230072969 + 3 ^ 40 * 6295857 * 2
def baseEnd_6295857 : Nat := 1077600257657959721411129

theorem tailTrace_6295857 : CollatzResearch.WordTrace tailWord_6295857 prefixEnd_6295857 1077600257657959721411129 := by
  unfold tailWord_6295857
  simp only [CollatzResearch.WordTrace]
  refine ⟨229628769552192810615941825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153085846368128540410627883 229628769552192810615941825)
  ·
    refine ⟨172221577164144607961956369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229628769552192810615941825 172221577164144607961956369)
    ·
      refine ⟨129166182873108455971467277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172221577164144607961956369 129166182873108455971467277)
      ·
        refine ⟨48437318577415670989300229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129166182873108455971467277 48437318577415670989300229)
        ·
          refine ⟨9081997233265438310493793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48437318577415670989300229 9081997233265438310493793)
          ·
            refine ⟨6811497924949078732870345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9081997233265438310493793 6811497924949078732870345)
            ·
              refine ⟨5108623443711809049652759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6811497924949078732870345 5108623443711809049652759)
              ·
                refine ⟨7662935165567713574479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108623443711809049652759 7662935165567713574479139)
                ·
                  refine ⟨11494402748351570361718709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662935165567713574479139 11494402748351570361718709)
                  ·
                    refine ⟨1077600257657959721411129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11494402748351570361718709 1077600257657959721411129)
                    ·
                      rfl

theorem cell23_6295857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_6295857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295857 prefixEnd_6295857 := by exact prefixLift 6295857
  have htrace : WordTrace (prefixWord ++ tailWord_6295857) baseStart_6295857 baseEnd_6295857 := by
    simpa [prefixWord, tailWord_6295857, baseEnd_6295857] using wordTrace_append hprefix tailTrace_6295857
  have hstable : (prefixWord ++ tailWord_6295857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295857).length < 2 ^ (prefixWord ++ tailWord_6295857).sum := by decide
  have hdescent : baseEnd_6295857 < baseStart_6295857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295866 : List Nat := [3, 1, 1, 1, 4, 3, 10]
def baseStart_6295866 : Nat := 118140960795 + 6295866 * 2 ^ 59
def prefixEnd_6295866 : Nat := 4983230072969 + 3 ^ 40 * 6295866 * 2
def baseEnd_6295866 : Nat := 39911177707404563321245

theorem tailTrace_6295866 : CollatzResearch.WordTrace tailWord_6295866 prefixEnd_6295866 39911177707404563321245 := by
  unfold tailWord_6295866
  simp only [CollatzResearch.WordTrace]
  refine ⟨57407274452290051288254863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153086065206106803435346301 57407274452290051288254863)
  ·
    refine ⟨86110911678435076932382295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57407274452290051288254863 86110911678435076932382295)
    ·
      refine ⟨129166367517652615398573443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86110911678435076932382295 129166367517652615398573443)
      ·
        refine ⟨193749551276478923097860165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129166367517652615398573443 193749551276478923097860165)
        ·
          refine ⟨36328040864339798080848781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193749551276478923097860165 36328040864339798080848781)
          ·
            refine ⟨13623015324127424280318293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36328040864339798080848781 13623015324127424280318293)
            ·
              refine ⟨39911177707404563321245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13623015324127424280318293 39911177707404563321245)
              ·
                rfl

theorem cell23_6295866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 10].length) (baseStart_6295866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295866 prefixEnd_6295866 := by exact prefixLift 6295866
  have htrace : WordTrace (prefixWord ++ tailWord_6295866) baseStart_6295866 baseEnd_6295866 := by
    simpa [prefixWord, tailWord_6295866, baseEnd_6295866] using wordTrace_append hprefix tailTrace_6295866
  have hstable : (prefixWord ++ tailWord_6295866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295866).length < 2 ^ (prefixWord ++ tailWord_6295866).sum := by decide
  have hdescent : baseEnd_6295866 < baseStart_6295866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295870 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_6295870 : Nat := 118140960795 + 6295870 * 2 ^ 59
def prefixEnd_6295870 : Nat := 4983230072969 + 3 ^ 40 * 6295870 * 2
def baseEnd_6295870 : Nat := 1077602482740795871123609

theorem tailTrace_6295870 : CollatzResearch.WordTrace tailWord_6295870 prefixEnd_6295870 1077602482740795871123609 := by
  unfold tailWord_6295870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28703655462643214229520633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153086162467430475890776709 28703655462643214229520633)
  ·
    refine ⟨21527741596982410672140475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28703655462643214229520633 21527741596982410672140475)
    ·
      refine ⟨32291612395473616008210713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527741596982410672140475 32291612395473616008210713)
      ·
        refine ⟨24218709296605212006158035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32291612395473616008210713 24218709296605212006158035)
        ·
          refine ⟨36328063944907818009237053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24218709296605212006158035 36328063944907818009237053)
          ·
            refine ⟨13623023979340431753463895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36328063944907818009237053 13623023979340431753463895)
            ·
              refine ⟨20434535969010647630195843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13623023979340431753463895 20434535969010647630195843)
              ·
                refine ⟨30651803953515971445293765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20434535969010647630195843 30651803953515971445293765)
                ·
                  refine ⟨5747213241284244645992581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30651803953515971445293765 5747213241284244645992581)
                  ·
                    refine ⟨1077602482740795871123609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747213241284244645992581 1077602482740795871123609)
                    ·
                      rfl

theorem cell23_6295870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_6295870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295870 prefixEnd_6295870 := by exact prefixLift 6295870
  have htrace : WordTrace (prefixWord ++ tailWord_6295870) baseStart_6295870 baseEnd_6295870 := by
    simpa [prefixWord, tailWord_6295870, baseEnd_6295870] using wordTrace_append hprefix tailTrace_6295870
  have hstable : (prefixWord ++ tailWord_6295870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295870).length < 2 ^ (prefixWord ++ tailWord_6295870).sum := by decide
  have hdescent : baseEnd_6295870 < baseStart_6295870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295886 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6295886 : Nat := 118140960795 + 6295886 * 2 ^ 59
def prefixEnd_6295886 : Nat := 4983230072969 + 3 ^ 40 * 6295886 * 2
def baseEnd_6295886 : Nat := 3232815663912859550770753

theorem tailTrace_6295886 : CollatzResearch.WordTrace tailWord_6295886 prefixEnd_6295886 3232815663912859550770753 := by
  unfold tailWord_6295886
  simp only [CollatzResearch.WordTrace]
  refine ⟨28703728408635968571093439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153086551512725165712498341 28703728408635968571093439)
  ·
    refine ⟨43055592612953952856640159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28703728408635968571093439 43055592612953952856640159)
    ·
      refine ⟨64583388919430929284960239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43055592612953952856640159 64583388919430929284960239)
      ·
        refine ⟨96875083379146393927440359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64583388919430929284960239 96875083379146393927440359)
        ·
          refine ⟨145312625068719590891160539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96875083379146393927440359 145312625068719590891160539)
          ·
            refine ⟨217968937603079386336740809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145312625068719590891160539 217968937603079386336740809)
            ·
              refine ⟨163476703202309539752555607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217968937603079386336740809 163476703202309539752555607)
              ·
                refine ⟨245215054803464309628833411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163476703202309539752555607 245215054803464309628833411)
                ·
                  refine ⟨367822582205196464443250117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245215054803464309628833411 367822582205196464443250117)
                  ·
                    refine ⟨68966734163474337083109397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 367822582205196464443250117 68966734163474337083109397)
                    ·
                      refine ⟨3232815663912859550770753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68966734163474337083109397 3232815663912859550770753)
                      ·
                        rfl

theorem cell23_6295886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6295886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295886 prefixEnd_6295886 := by exact prefixLift 6295886
  have htrace : WordTrace (prefixWord ++ tailWord_6295886) baseStart_6295886 baseEnd_6295886 := by
    simpa [prefixWord, tailWord_6295886, baseEnd_6295886] using wordTrace_append hprefix tailTrace_6295886
  have hstable : (prefixWord ++ tailWord_6295886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295886).length < 2 ^ (prefixWord ++ tailWord_6295886).sum := by decide
  have hdescent : baseEnd_6295886 < baseStart_6295886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295900 : List Nat := [2, 2, 4, 3, 1, 1, 1, 9]
def baseStart_6295900 : Nat := 118140960795 + 6295900 * 2 ^ 59
def prefixEnd_6295900 : Nat := 4983230072969 + 3 ^ 40 * 6295900 * 2
def baseEnd_6295900 : Nat := 119734179727482314666507

theorem tailTrace_6295900 : CollatzResearch.WordTrace tailWord_6295900 prefixEnd_6295900 119734179727482314666507 := by
  unfold tailWord_6295900
  simp only [CollatzResearch.WordTrace]
  refine ⟨114815168945518514479878577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153086891927358019306504769 114815168945518514479878577)
  ·
    refine ⟨86111376709138885859908933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114815168945518514479878577 86111376709138885859908933)
    ·
      refine ⟨16145883132963541098732925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86111376709138885859908933 16145883132963541098732925)
      ·
        refine ⟨6054706174861327912024847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16145883132963541098732925 6054706174861327912024847)
        ·
          refine ⟨9082059262291991868037271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054706174861327912024847 9082059262291991868037271)
          ·
            refine ⟨13623088893437987802055907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082059262291991868037271 13623088893437987802055907)
            ·
              refine ⟨20434633340156981703083861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13623088893437987802055907 20434633340156981703083861)
              ·
                refine ⟨119734179727482314666507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20434633340156981703083861 119734179727482314666507)
                ·
                  rfl

theorem cell23_6295900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 9].length) (baseStart_6295900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295900 prefixEnd_6295900 := by exact prefixLift 6295900
  have htrace : WordTrace (prefixWord ++ tailWord_6295900) baseStart_6295900 baseEnd_6295900 := by
    simpa [prefixWord, tailWord_6295900, baseEnd_6295900] using wordTrace_append hprefix tailTrace_6295900
  have hstable : (prefixWord ++ tailWord_6295900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295900).length < 2 ^ (prefixWord ++ tailWord_6295900).sum := by decide
  have hdescent : baseEnd_6295900 < baseStart_6295900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295911 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_6295911 : Nat := 118140960795 + 6295911 * 2 ^ 59
def prefixEnd_6295911 : Nat := 4983230072969 + 3 ^ 40 * 6295911 * 2
def baseEnd_6295911 : Nat := 3232828500929221952958139

theorem tailTrace_6295911 : CollatzResearch.WordTrace tailWord_6295911 prefixEnd_6295911 3232828500929221952958139 := by
  unfold tailWord_6295911
  simp only [CollatzResearch.WordTrace]
  refine ⟨229630739093997177838407587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153087159395998118558938391 229630739093997177838407587)
  ·
    refine ⟨344446108640995766757611381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229630739093997177838407587 344446108640995766757611381)
    ·
      refine ⟨32291822685093353133526067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 344446108640995766757611381 32291822685093353133526067)
      ·
        refine ⟨48437734027640029700289101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32291822685093353133526067 48437734027640029700289101)
        ·
          refine ⟨18164150260365011137608413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48437734027640029700289101 18164150260365011137608413)
          ·
            refine ⟨6811556347636879176603155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18164150260365011137608413 6811556347636879176603155)
            ·
              refine ⟨10217334521455318764904733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811556347636879176603155 10217334521455318764904733)
              ·
                refine ⟨3831500445545744536839275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10217334521455318764904733 3831500445545744536839275)
                ·
                  refine ⟨5747250668318616805258913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831500445545744536839275 5747250668318616805258913)
                  ·
                    refine ⟨4310438001238962603944185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5747250668318616805258913 4310438001238962603944185)
                    ·
                      refine ⟨3232828500929221952958139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310438001238962603944185 3232828500929221952958139)
                      ·
                        rfl

theorem cell23_6295911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_6295911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295911 prefixEnd_6295911 := by exact prefixLift 6295911
  have htrace : WordTrace (prefixWord ++ tailWord_6295911) baseStart_6295911 baseEnd_6295911 := by
    simpa [prefixWord, tailWord_6295911, baseEnd_6295911] using wordTrace_append hprefix tailTrace_6295911
  have hstable : (prefixWord ++ tailWord_6295911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295911).length < 2 ^ (prefixWord ++ tailWord_6295911).sum := by decide
  have hdescent : baseEnd_6295911 < baseStart_6295911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295938 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6295938 : Nat := 118140960795 + 6295938 * 2 ^ 59
def prefixEnd_6295938 : Nat := 4983230072969 + 3 ^ 40 * 6295938 * 2
def baseEnd_6295938 : Nat := 1077614121635631115773505

theorem tailTrace_6295938 : CollatzResearch.WordTrace tailWord_6295938 prefixEnd_6295938 1077614121635631115773505 := by
  unfold tailWord_6295938
  simp only [CollatzResearch.WordTrace]
  refine ⟨57407930966224840362410117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153087815909932907633093645 57407930966224840362410117)
  ·
    refine ⟨10763987056167157567951897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57407930966224840362410117 10763987056167157567951897)
    ·
      refine ⟨8072990292125368175963923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10763987056167157567951897 8072990292125368175963923)
      ·
        refine ⟨12109485438188052263945885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8072990292125368175963923 12109485438188052263945885)
        ·
          refine ⟨4541057039320519598979707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12109485438188052263945885 4541057039320519598979707)
          ·
            refine ⟨6811585558980779398469561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541057039320519598979707 6811585558980779398469561)
            ·
              refine ⟨5108689169235584548852171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6811585558980779398469561 5108689169235584548852171)
              ·
                refine ⟨7663033753853376823278257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108689169235584548852171 7663033753853376823278257)
                ·
                  refine ⟨5747275315390032617458693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7663033753853376823278257 5747275315390032617458693)
                  ·
                    refine ⟨1077614121635631115773505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747275315390032617458693 1077614121635631115773505)
                    ·
                      rfl

theorem cell23_6295938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6295938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295938 prefixEnd_6295938 := by exact prefixLift 6295938
  have htrace : WordTrace (prefixWord ++ tailWord_6295938) baseStart_6295938 baseEnd_6295938 := by
    simpa [prefixWord, tailWord_6295938, baseEnd_6295938] using wordTrace_append hprefix tailTrace_6295938
  have hstable : (prefixWord ++ tailWord_6295938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295938).length < 2 ^ (prefixWord ++ tailWord_6295938).sum := by decide
  have hdescent : baseEnd_6295938 < baseStart_6295938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295978 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6295978 : Nat := 118140960795 + 6295978 * 2 ^ 59
def prefixEnd_6295978 : Nat := 4983230072969 + 3 ^ 40 * 6295978 * 2
def baseEnd_6295978 : Nat := 3232862904133073190820331

theorem tailTrace_6295978 : CollatzResearch.WordTrace tailWord_6295978 prefixEnd_6295978 3232862904133073190820331 := by
  unfold tailWord_6295978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57408295696188612070274147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153088788523169632187397725 57408295696188612070274147)
  ·
    refine ⟨86112443544282918105411221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57408295696188612070274147 86112443544282918105411221)
    ·
      refine ⟨4036520791138261786191151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86112443544282918105411221 4036520791138261786191151)
      ·
        refine ⟨6054781186707392679286727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4036520791138261786191151 6054781186707392679286727)
        ·
          refine ⟨9082171780061089018930091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6054781186707392679286727 9082171780061089018930091)
          ·
            refine ⟨13623257670091633528395137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082171780061089018930091 13623257670091633528395137)
            ·
              refine ⟨10217443252568725146296353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13623257670091633528395137 10217443252568725146296353)
              ·
                refine ⟨7663082439426543859722265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10217443252568725146296353 7663082439426543859722265)
                ·
                  refine ⟨5747311829569907894791699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7663082439426543859722265 5747311829569907894791699)
                  ·
                    refine ⟨8620967744354861842187549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5747311829569907894791699 8620967744354861842187549)
                    ·
                      refine ⟨3232862904133073190820331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8620967744354861842187549 3232862904133073190820331)
                      ·
                        rfl

theorem cell23_6295978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6295978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6295978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6295978 prefixEnd_6295978 := by exact prefixLift 6295978
  have htrace : WordTrace (prefixWord ++ tailWord_6295978) baseStart_6295978 baseEnd_6295978 := by
    simpa [prefixWord, tailWord_6295978, baseEnd_6295978] using wordTrace_append hprefix tailTrace_6295978
  have hstable : (prefixWord ++ tailWord_6295978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295978).length < 2 ^ (prefixWord ++ tailWord_6295978).sum := by decide
  have hdescent : baseEnd_6295978 < baseStart_6295978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296010 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_6296010 : Nat := 118140960795 + 6296010 * 2 ^ 59
def prefixEnd_6296010 : Nat := 4983230072969 + 3 ^ 40 * 6296010 * 2
def baseEnd_6296010 : Nat := 3232879335514017065620183

theorem tailTrace_6296010 : CollatzResearch.WordTrace tailWord_6296010 prefixEnd_6296010 3232879335514017065620183 := by
  unfold tailWord_6296010
  simp only [CollatzResearch.WordTrace]
  refine ⟨57408587480159629436565371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153089566613759011830840989 57408587480159629436565371)
  ·
    refine ⟨86112881220239444154848057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57408587480159629436565371 86112881220239444154848057)
    ·
      refine ⟨64584660915179583116136043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86112881220239444154848057 64584660915179583116136043)
      ·
        refine ⟨96876991372769374674204065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64584660915179583116136043 96876991372769374674204065)
        ·
          refine ⟨72657743529577031005653049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96876991372769374674204065 72657743529577031005653049)
          ·
            refine ⟨54493307647182773254239787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72657743529577031005653049 54493307647182773254239787)
            ·
              refine ⟨81739961470774159881359681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54493307647182773254239787 81739961470774159881359681)
              ·
                refine ⟨61304971103080619911019761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81739961470774159881359681 61304971103080619911019761)
                ·
                  refine ⟨45978728327310464933264821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61304971103080619911019761 45978728327310464933264821)
                  ·
                    refine ⟨4310505780685356087493577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45978728327310464933264821 4310505780685356087493577)
                    ·
                      refine ⟨3232879335514017065620183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310505780685356087493577 3232879335514017065620183)
                      ·
                        rfl

theorem cell23_6296010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_6296010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296010 prefixEnd_6296010 := by exact prefixLift 6296010
  have htrace : WordTrace (prefixWord ++ tailWord_6296010) baseStart_6296010 baseEnd_6296010 := by
    simpa [prefixWord, tailWord_6296010, baseEnd_6296010] using wordTrace_append hprefix tailTrace_6296010
  have hstable : (prefixWord ++ tailWord_6296010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296010).length < 2 ^ (prefixWord ++ tailWord_6296010).sum := by decide
  have hdescent : baseEnd_6296010 < baseStart_6296010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296020 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_6296020 : Nat := 118140960795 + 6296020 * 2 ^ 59
def prefixEnd_6296020 : Nat := 4983230072969 + 3 ^ 40 * 6296020 * 2
def baseEnd_6296020 : Nat := 1077628156773520675498379

theorem tailTrace_6296020 : CollatzResearch.WordTrace tailWord_6296020 prefixEnd_6296020 1077628156773520675498379 := by
  unfold tailWord_6296020
  simp only [CollatzResearch.WordTrace]
  refine ⟨114817357325301144727062757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153089809767068192969417009 114817357325301144727062757)
  ·
    refine ⟨21528254498493964636324267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114817357325301144727062757 21528254498493964636324267)
    ·
      refine ⟨32292381747740946954486401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21528254498493964636324267 32292381747740946954486401)
      ·
        refine ⟨24219286310805710215864801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32292381747740946954486401 24219286310805710215864801)
        ·
          refine ⟨18164464733104282661898601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24219286310805710215864801 18164464733104282661898601)
          ·
            refine ⟨13623348549828211996423951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18164464733104282661898601 13623348549828211996423951)
            ·
              refine ⟨20435022824742317994635927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13623348549828211996423951 20435022824742317994635927)
              ·
                refine ⟨30652534237113476991953891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20435022824742317994635927 30652534237113476991953891)
                ·
                  refine ⟨45978801355670215487930837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30652534237113476991953891 45978801355670215487930837)
                  ·
                    refine ⟨1077628156773520675498379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45978801355670215487930837 1077628156773520675498379)
                    ·
                      rfl

theorem cell23_6296020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_6296020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296020 prefixEnd_6296020 := by exact prefixLift 6296020
  have htrace : WordTrace (prefixWord ++ tailWord_6296020) baseStart_6296020 baseEnd_6296020 := by
    simpa [prefixWord, tailWord_6296020, baseEnd_6296020] using wordTrace_append hprefix tailTrace_6296020
  have hstable : (prefixWord ++ tailWord_6296020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296020).length < 2 ^ (prefixWord ++ tailWord_6296020).sum := by decide
  have hdescent : baseEnd_6296020 < baseStart_6296020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296117 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_6296117 : Nat := 118140960795 + 6296117 * 2 ^ 59
def prefixEnd_6296117 : Nat := 4983230072969 + 3 ^ 40 * 6296117 * 2
def baseEnd_6296117 : Nat := 3232934277944048146982191

theorem tailTrace_6296117 : CollatzResearch.WordTrace tailWord_6296117 prefixEnd_6296117 3232934277944048146982191 := by
  unfold tailWord_6296117
  simp only [CollatzResearch.WordTrace]
  refine ⟨229638252531250875020406605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153092168354167250013604403 229638252531250875020406605)
  ·
    refine ⟨86114344699219078132652477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229638252531250875020406605 86114344699219078132652477)
    ·
      refine ⟨32292879262207154299744679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86114344699219078132652477 32292879262207154299744679)
      ·
        refine ⟨48439318893310731449617019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32292879262207154299744679 48439318893310731449617019)
        ·
          refine ⟨72658978339966097174425529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48439318893310731449617019 72658978339966097174425529)
          ·
            refine ⟨54494233754974572880819147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72658978339966097174425529 54494233754974572880819147)
            ·
              refine ⟨81741350632461859321228721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54494233754974572880819147 81741350632461859321228721)
              ·
                refine ⟨61306012974346394490921541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81741350632461859321228721 61306012974346394490921541)
                ·
                  refine ⟨11494877432689948967047789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61306012974346394490921541 11494877432689948967047789)
                  ·
                    refine ⟨4310579037258730862642921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11494877432689948967047789 4310579037258730862642921)
                    ·
                      refine ⟨3232934277944048146982191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310579037258730862642921 3232934277944048146982191)
                      ·
                        rfl

theorem cell23_6296117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_6296117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296117 prefixEnd_6296117 := by exact prefixLift 6296117
  have htrace : WordTrace (prefixWord ++ tailWord_6296117) baseStart_6296117 baseEnd_6296117 := by
    simpa [prefixWord, tailWord_6296117, baseEnd_6296117] using wordTrace_append hprefix tailTrace_6296117
  have hstable : (prefixWord ++ tailWord_6296117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296117).length < 2 ^ (prefixWord ++ tailWord_6296117).sum := by decide
  have hdescent : baseEnd_6296117 < baseStart_6296117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296140 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_6296140 : Nat := 118140960795 + 6296140 * 2 ^ 59
def prefixEnd_6296140 : Nat := 4983230072969 + 3 ^ 40 * 6296140 * 2
def baseEnd_6296140 : Nat := 1077648695999700518998195

theorem tailTrace_6296140 : CollatzResearch.WordTrace tailWord_6296140 prefixEnd_6296140 1077648695999700518998195 := by
  unfold tailWord_6296140
  simp only [CollatzResearch.WordTrace]
  refine ⟨114819545705083774974246937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153092727606778366632329249 114819545705083774974246937)
  ·
    refine ⟨86114659278812831230685203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114819545705083774974246937 86114659278812831230685203)
    ·
      refine ⟨129171988918219246846027805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86114659278812831230685203 129171988918219246846027805)
      ·
        refine ⟨48439495844332217567260427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129171988918219246846027805 48439495844332217567260427)
        ·
          refine ⟨72659243766498326350890641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48439495844332217567260427 72659243766498326350890641)
          ·
            refine ⟨54494432824873744763167981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72659243766498326350890641 54494432824873744763167981)
            ·
              refine ⟨20435412309327654286187993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54494432824873744763167981 20435412309327654286187993)
              ·
                refine ⟨15326559231995740714640995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20435412309327654286187993 15326559231995740714640995)
                ·
                  refine ⟨22989838847993611071961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15326559231995740714640995 22989838847993611071961493)
                  ·
                    refine ⟨1077648695999700518998195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22989838847993611071961493 1077648695999700518998195)
                    ·
                      rfl

theorem cell23_6296140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_6296140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296140 prefixEnd_6296140 := by exact prefixLift 6296140
  have htrace : WordTrace (prefixWord ++ tailWord_6296140) baseStart_6296140 baseEnd_6296140 := by
    simpa [prefixWord, tailWord_6296140, baseEnd_6296140] using wordTrace_append hprefix tailTrace_6296140
  have hstable : (prefixWord ++ tailWord_6296140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296140).length < 2 ^ (prefixWord ++ tailWord_6296140).sum := by decide
  have hdescent : baseEnd_6296140 < baseStart_6296140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296164 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_6296164 : Nat := 118140960795 + 6296164 * 2 ^ 59
def prefixEnd_6296164 : Nat := 4983230072969 + 3 ^ 40 * 6296164 * 2
def baseEnd_6296164 : Nat := 3232958411534809463094475

theorem tailTrace_6296164 : CollatzResearch.WordTrace tailWord_6296164 prefixEnd_6296164 3232958411534809463094475 := by
  unfold tailWord_6296164
  simp only [CollatzResearch.WordTrace]
  refine ⟨114819983381040301023683773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153093311174720401364911697 114819983381040301023683773)
  ·
    refine ⟨43057493767890112883881415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114819983381040301023683773 43057493767890112883881415)
    ·
      refine ⟨64586240651835169325822123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43057493767890112883881415 64586240651835169325822123)
      ·
        refine ⟨96879360977752753988733185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64586240651835169325822123 96879360977752753988733185)
        ·
          refine ⟨72659520733314565491549889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96879360977752753988733185 72659520733314565491549889)
          ·
            refine ⟨54494640549985924118662417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72659520733314565491549889 54494640549985924118662417)
            ·
              refine ⟨40870980412489443088996813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54494640549985924118662417 40870980412489443088996813)
              ·
                refine ⟨15326617654683541158373805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40870980412489443088996813 15326617654683541158373805)
                ·
                  refine ⟨5747481620506327934390177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15326617654683541158373805 5747481620506327934390177)
                  ·
                    refine ⟨4310611215379745950792633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5747481620506327934390177 4310611215379745950792633)
                    ·
                      refine ⟨3232958411534809463094475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310611215379745950792633 3232958411534809463094475)
                      ·
                        rfl

theorem cell23_6296164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_6296164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296164 prefixEnd_6296164 := by exact prefixLift 6296164
  have htrace : WordTrace (prefixWord ++ tailWord_6296164) baseStart_6296164 baseEnd_6296164 := by
    simpa [prefixWord, tailWord_6296164, baseEnd_6296164] using wordTrace_append hprefix tailTrace_6296164
  have hstable : (prefixWord ++ tailWord_6296164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296164).length < 2 ^ (prefixWord ++ tailWord_6296164).sum := by decide
  have hdescent : baseEnd_6296164 < baseStart_6296164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296174 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_6296174 : Nat := 118140960795 + 6296174 * 2 ^ 59
def prefixEnd_6296174 : Nat := 4983230072969 + 3 ^ 40 * 6296174 * 2
def baseEnd_6296174 : Nat := 1077654515447118141323143

theorem tailTrace_6296174 : CollatzResearch.WordTrace tailWord_6296174 prefixEnd_6296174 1077654515447118141323143 := by
  unfold tailWord_6296174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28705041436505546719403947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153093554328029582503487717 28705041436505546719403947)
  ·
    refine ⟨43057562154758320079105921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28705041436505546719403947 43057562154758320079105921)
    ·
      refine ⟨32293171616068740059329441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43057562154758320079105921 32293171616068740059329441)
      ·
        refine ⟨24219878712051555044497081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32293171616068740059329441 24219878712051555044497081)
        ·
          refine ⟨18164909034038666283372811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24219878712051555044497081 18164909034038666283372811)
          ·
            refine ⟨27247363551057999425059217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18164909034038666283372811 27247363551057999425059217)
            ·
              refine ⟨20435522663293499568794413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27247363551057999425059217 20435522663293499568794413)
              ·
                refine ⟨7663320998735062338297905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20435522663293499568794413 7663320998735062338297905)
                ·
                  refine ⟨5747490749051296753723429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7663320998735062338297905 5747490749051296753723429)
                  ·
                    refine ⟨1077654515447118141323143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747490749051296753723429 1077654515447118141323143)
                    ·
                      rfl

theorem cell23_6296174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_6296174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296174 prefixEnd_6296174 := by exact prefixLift 6296174
  have htrace : WordTrace (prefixWord ++ tailWord_6296174) baseStart_6296174 baseEnd_6296174 := by
    simpa [prefixWord, tailWord_6296174, baseEnd_6296174] using wordTrace_append hprefix tailTrace_6296174
  have hstable : (prefixWord ++ tailWord_6296174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296174).length < 2 ^ (prefixWord ++ tailWord_6296174).sum := by decide
  have hdescent : baseEnd_6296174 < baseStart_6296174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296197 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_6296197 : Nat := 118140960795 + 6296197 * 2 ^ 59
def prefixEnd_6296197 : Nat := 4983230072969 + 3 ^ 40 * 6296197 * 2
def baseEnd_6296197 : Nat := 3232975356396407833981823

theorem tailTrace_6296197 : CollatzResearch.WordTrace tailWord_6296197 prefixEnd_6296197 3232975356396407833981823 := by
  unfold tailWord_6296197
  simp only [CollatzResearch.WordTrace]
  refine ⟨229641170370961048683318845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153094113580640699122212563 229641170370961048683318845)
  ·
    refine ⟨86115438889110393256244567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229641170370961048683318845 86115438889110393256244567)
    ·
      refine ⟨129173158333665589884366851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86115438889110393256244567 129173158333665589884366851)
      ·
        refine ⟨193759737500498384826550277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129173158333665589884366851 193759737500498384826550277)
        ·
          refine ⟨36329950781343447154978177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193759737500498384826550277 36329950781343447154978177)
          ·
            refine ⟨27247463086007585366233633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36329950781343447154978177 27247463086007585366233633)
            ·
              refine ⟨20435597314505689024675225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27247463086007585366233633 20435597314505689024675225)
              ·
                refine ⟨15326697985879266768506419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20435597314505689024675225 15326697985879266768506419)
                ·
                  refine ⟨22990046978818900152759629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15326697985879266768506419 22990046978818900152759629)
                  ·
                    refine ⟨8621267617057087557284861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22990046978818900152759629 8621267617057087557284861)
                    ·
                      refine ⟨3232975356396407833981823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8621267617057087557284861 3232975356396407833981823)
                      ·
                        rfl

theorem cell23_6296197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_6296197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296197 prefixEnd_6296197 := by exact prefixLift 6296197
  have htrace : WordTrace (prefixWord ++ tailWord_6296197) baseStart_6296197 baseEnd_6296197 := by
    simpa [prefixWord, tailWord_6296197, baseEnd_6296197] using wordTrace_append hprefix tailTrace_6296197
  have hstable : (prefixWord ++ tailWord_6296197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296197).length < 2 ^ (prefixWord ++ tailWord_6296197).sum := by decide
  have hdescent : baseEnd_6296197 < baseStart_6296197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296240 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_6296240 : Nat := 118140960795 + 6296240 * 2 ^ 59
def prefixEnd_6296240 : Nat := 4983230072969 + 3 ^ 40 * 6296240 * 2
def baseEnd_6296240 : Nat := 3232997436064551165744125

theorem tailTrace_6296240 : CollatzResearch.WordTrace tailWord_6296240 prefixEnd_6296240 3232997436064551165744125 := by
  unfold tailWord_6296240
  simp only [CollatzResearch.WordTrace]
  refine ⟨114821369354902633513567087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153095159139870178018089449 114821369354902633513567087)
  ·
    refine ⟨172232054032353950270350631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114821369354902633513567087 172232054032353950270350631)
    ·
      refine ⟨258348081048530925405525947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172232054032353950270350631 258348081048530925405525947)
      ·
        refine ⟨387522121572796388108288921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258348081048530925405525947 387522121572796388108288921)
        ·
          refine ⟨290641591179597291081216691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387522121572796388108288921 290641591179597291081216691)
          ·
            refine ⟨435962386769395936621825037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290641591179597291081216691 435962386769395936621825037)
            ·
              refine ⟨163485895038523476233184389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435962386769395936621825037 163485895038523476233184389)
              ·
                refine ⟨30653605319723151793722073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163485895038523476233184389 30653605319723151793722073)
                ·
                  refine ⟨22990203989792363845291555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30653605319723151793722073 22990203989792363845291555)
                  ·
                    refine ⟨34485305984688545767937333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22990203989792363845291555 34485305984688545767937333)
                    ·
                      refine ⟨3232997436064551165744125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34485305984688545767937333 3232997436064551165744125)
                      ·
                        rfl

theorem cell23_6296240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_6296240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296240 prefixEnd_6296240 := by exact prefixLift 6296240
  have htrace : WordTrace (prefixWord ++ tailWord_6296240) baseStart_6296240 baseEnd_6296240 := by
    simpa [prefixWord, tailWord_6296240, baseEnd_6296240] using wordTrace_append hprefix tailTrace_6296240
  have hstable : (prefixWord ++ tailWord_6296240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296240).length < 2 ^ (prefixWord ++ tailWord_6296240).sum := by decide
  have hdescent : baseEnd_6296240 < baseStart_6296240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296254 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_6296254 : Nat := 118140960795 + 6296254 * 2 ^ 59
def prefixEnd_6296254 : Nat := 4983230072969 + 3 ^ 40 * 6296254 * 2
def baseEnd_6296254 : Nat := 3233004624793714110969061

theorem tailTrace_6296254 : CollatzResearch.WordTrace tailWord_6296254 prefixEnd_6296254 3233004624793714110969061 := by
  unfold tailWord_6296254
  simp only [CollatzResearch.WordTrace]
  refine ⟨28705406166469318427267977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153095499554503031612095877 28705406166469318427267977)
  ·
    refine ⟨21529054624851988820450983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28705406166469318427267977 21529054624851988820450983)
    ·
      refine ⟨32293581937277983230676475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21529054624851988820450983 32293581937277983230676475)
      ·
        refine ⟨48440372905916974846014713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32293581937277983230676475 48440372905916974846014713)
        ·
          refine ⟨36330279679437731134511035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48440372905916974846014713 36330279679437731134511035)
          ·
            refine ⟨54495419519156596701766553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36330279679437731134511035 54495419519156596701766553)
            ·
              refine ⟨40871564639367447526324915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54495419519156596701766553 40871564639367447526324915)
              ·
                refine ⟨61307346959051171289487373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40871564639367447526324915 61307346959051171289487373)
                ·
                  refine ⟨22990255109644189233557765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61307346959051171289487373 22990255109644189233557765)
                  ·
                    refine ⟨4310672833058285481292081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22990255109644189233557765 4310672833058285481292081)
                    ·
                      refine ⟨3233004624793714110969061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310672833058285481292081 3233004624793714110969061)
                      ·
                        rfl

theorem cell23_6296254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_6296254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296254 prefixEnd_6296254 := by exact prefixLift 6296254
  have htrace : WordTrace (prefixWord ++ tailWord_6296254) baseStart_6296254 baseEnd_6296254 := by
    simpa [prefixWord, tailWord_6296254, baseEnd_6296254] using wordTrace_append hprefix tailTrace_6296254
  have hstable : (prefixWord ++ tailWord_6296254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296254).length < 2 ^ (prefixWord ++ tailWord_6296254).sum := by decide
  have hdescent : baseEnd_6296254 < baseStart_6296254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296300 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_6296300 : Nat := 118140960795 + 6296300 * 2 ^ 59
def prefixEnd_6296300 : Nat := 4983230072969 + 3 ^ 40 * 6296300 * 2
def baseEnd_6296300 : Nat := 3233028244903820930993849

theorem tailTrace_6296300 : CollatzResearch.WordTrace tailWord_6296300 prefixEnd_6296300 3233028244903820930993849 := by
  unfold tailWord_6296300
  simp only [CollatzResearch.WordTrace]
  refine ⟨114822463544793948637159177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153096618059725264849545569 114822463544793948637159177)
  ·
    refine ⟨86116847658595461477869383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114822463544793948637159177 86116847658595461477869383)
    ·
      refine ⟨129175271487893192216804075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86116847658595461477869383 129175271487893192216804075)
      ·
        refine ⟨193762907231839788325206113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129175271487893192216804075 193762907231839788325206113)
        ·
          refine ⟨145322180423879841243904585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193762907231839788325206113 145322180423879841243904585)
          ·
            refine ⟨108991635317909880932928439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145322180423879841243904585 108991635317909880932928439)
            ·
              refine ⟨163487452976864821399392659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108991635317909880932928439 163487452976864821399392659)
              ·
                refine ⟨245231179465297232099088989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163487452976864821399392659 245231179465297232099088989)
                ·
                  refine ⟨91961692299486462037158371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245231179465297232099088989 91961692299486462037158371)
                  ·
                    refine ⟨137942538449229693055737557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91961692299486462037158371 137942538449229693055737557)
                    ·
                      refine ⟨3233028244903820930993849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137942538449229693055737557 3233028244903820930993849)
                      ·
                        rfl

theorem cell23_6296300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_6296300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296300 prefixEnd_6296300 := by exact prefixLift 6296300
  have htrace : WordTrace (prefixWord ++ tailWord_6296300) baseStart_6296300 baseEnd_6296300 := by
    simpa [prefixWord, tailWord_6296300, baseEnd_6296300] using wordTrace_append hprefix tailTrace_6296300
  have hstable : (prefixWord ++ tailWord_6296300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296300).length < 2 ^ (prefixWord ++ tailWord_6296300).sum := by decide
  have hdescent : baseEnd_6296300 < baseStart_6296300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296354 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6296354 : Nat := 118140960795 + 6296354 * 2 ^ 59
def prefixEnd_6296354 : Nat := 4983230072969 + 3 ^ 40 * 6296354 * 2
def baseEnd_6296354 : Nat := 1077685324286387906572867

theorem tailTrace_6296354 : CollatzResearch.WordTrace tailWord_6296354 prefixEnd_6296354 1077685324286387906572867 := by
  unfold tailWord_6296354
  simp only [CollatzResearch.WordTrace]
  refine ⟨57411724157848066124196029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153097931087594842997856077 57411724157848066124196029)
  ·
    refine ⟨21529396559193024796573511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57411724157848066124196029 21529396559193024796573511)
    ·
      refine ⟨32294094838789537194860267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21529396559193024796573511 32294094838789537194860267)
      ·
        refine ⟨48441142258184305792290401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32294094838789537194860267 48441142258184305792290401)
        ·
          refine ⟨36330856693638229344217801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48441142258184305792290401 36330856693638229344217801)
          ·
            refine ⟨27248142520228672008163351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36330856693638229344217801 27248142520228672008163351)
            ·
              refine ⟨40872213780343008012245027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27248142520228672008163351 40872213780343008012245027)
              ·
                refine ⟨61308320670514512018367541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40872213780343008012245027 61308320670514512018367541)
                ·
                  refine ⟨5747655062860735501721957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61308320670514512018367541 5747655062860735501721957)
                  ·
                    refine ⟨1077685324286387906572867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747655062860735501721957 1077685324286387906572867)
                    ·
                      rfl

theorem cell23_6296354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6296354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296354 prefixEnd_6296354 := by exact prefixLift 6296354
  have htrace : WordTrace (prefixWord ++ tailWord_6296354) baseStart_6296354 baseEnd_6296354 := by
    simpa [prefixWord, tailWord_6296354, baseEnd_6296354] using wordTrace_append hprefix tailTrace_6296354
  have hstable : (prefixWord ++ tailWord_6296354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296354).length < 2 ^ (prefixWord ++ tailWord_6296354).sum := by decide
  have hdescent : baseEnd_6296354 < baseStart_6296354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296371 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 1, 4]
def baseStart_6296371 : Nat := 118140960795 + 6296371 * 2 ^ 59
def prefixEnd_6296371 : Nat := 4983230072969 + 3 ^ 40 * 6296371 * 2
def baseEnd_6296371 : Nat := 1077688234010096717735341

theorem tailTrace_6296371 : CollatzResearch.WordTrace tailWord_6296371 prefixEnd_6296371 1077688234010096717735341 := by
  unfold tailWord_6296371
  simp only [CollatzResearch.WordTrace]
  refine ⟨229647516672330676400152967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153098344448220450933435311 229647516672330676400152967)
  ·
    refine ⟨344471275008496014600229451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229647516672330676400152967 344471275008496014600229451)
    ·
      refine ⟨516706912512744021900344177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344471275008496014600229451 516706912512744021900344177)
      ·
        refine ⟨387530184384558016425258133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516706912512744021900344177 387530184384558016425258133)
        ·
          refine ⟨18165477393026157019933975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 387530184384558016425258133 18165477393026157019933975)
          ·
            refine ⟨27248216089539235529900963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18165477393026157019933975 27248216089539235529900963)
            ·
              refine ⟨40872324134308853294851445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27248216089539235529900963 40872324134308853294851445)
              ·
                refine ⟨3831780387591454996392323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40872324134308853294851445 3831780387591454996392323)
                ·
                  refine ⟨5747670581387182494588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831780387591454996392323 5747670581387182494588485)
                  ·
                    refine ⟨1077688234010096717735341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5747670581387182494588485 1077688234010096717735341)
                    ·
                      rfl

theorem cell23_6296371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 4].length) (baseStart_6296371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296371 prefixEnd_6296371 := by exact prefixLift 6296371
  have htrace : WordTrace (prefixWord ++ tailWord_6296371) baseStart_6296371 baseEnd_6296371 := by
    simpa [prefixWord, tailWord_6296371, baseEnd_6296371] using wordTrace_append hprefix tailTrace_6296371
  have hstable : (prefixWord ++ tailWord_6296371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296371).length < 2 ^ (prefixWord ++ tailWord_6296371).sum := by decide
  have hdescent : baseEnd_6296371 < baseStart_6296371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296401 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 6]
def baseStart_6296401 : Nat := 118140960795 + 6296401 * 2 ^ 59
def prefixEnd_6296401 : Nat := 4983230072969 + 3 ^ 40 * 6296401 * 2
def baseEnd_6296401 : Nat := 359231122938880559536765

theorem tailTrace_6296401 : CollatzResearch.WordTrace tailWord_6296401 prefixEnd_6296401 359231122938880559536765 := by
  unfold tailWord_6296401
  simp only [CollatzResearch.WordTrace]
  refine ⟨229648610862221991523745057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153099073908147994349163371 229648610862221991523745057)
  ·
    refine ⟨172236458146666493642808793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229648610862221991523745057 172236458146666493642808793)
    ·
      refine ⟨129177343609999870232106595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172236458146666493642808793 129177343609999870232106595)
      ·
        refine ⟨193766015414999805348159893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129177343609999870232106595 193766015414999805348159893)
        ·
          refine ⟨9082781972578115875694995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193766015414999805348159893 9082781972578115875694995)
          ·
            refine ⟨13624172958867173813542493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082781972578115875694995 13624172958867173813542493)
            ·
              refine ⟨5109064859575190180078435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13624172958867173813542493 5109064859575190180078435)
              ·
                refine ⟨7663597289362785270117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109064859575190180078435 7663597289362785270117653)
                ·
                  refine ⟨359231122938880559536765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7663597289362785270117653 359231122938880559536765)
                  ·
                    rfl

theorem cell23_6296401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 6].length) (baseStart_6296401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296401 prefixEnd_6296401 := by exact prefixLift 6296401
  have htrace : WordTrace (prefixWord ++ tailWord_6296401) baseStart_6296401 baseEnd_6296401 := by
    simpa [prefixWord, tailWord_6296401, baseEnd_6296401] using wordTrace_append hprefix tailTrace_6296401
  have hstable : (prefixWord ++ tailWord_6296401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296401).length < 2 ^ (prefixWord ++ tailWord_6296401).sum := by decide
  have hdescent : baseEnd_6296401 < baseStart_6296401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296427 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 1, 6]
def baseStart_6296427 : Nat := 118140960795 + 6296427 * 2 ^ 59
def prefixEnd_6296427 : Nat := 4983230072969 + 3 ^ 40 * 6296427 * 2
def baseEnd_6296427 : Nat := 1077697818982313978035255

theorem tailTrace_6296427 : CollatzResearch.WordTrace tailWord_6296427 prefixEnd_6296427 1077697818982313978035255 := by
  unfold tailWord_6296427
  simp only [CollatzResearch.WordTrace]
  refine ⟨229649559160127797964191535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153099706106751865309461023 229649559160127797964191535)
  ·
    refine ⟨344474338740191696946287303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229649559160127797964191535 344474338740191696946287303)
    ·
      refine ⟨516711508110287545419430955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344474338740191696946287303 516711508110287545419430955)
      ·
        refine ⟨775067262165431318129146433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516711508110287545419430955 775067262165431318129146433)
        ·
          refine ⟨581300446624073488596859825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775067262165431318129146433 581300446624073488596859825)
          ·
            refine ⟨435975334968055116447644869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581300446624073488596859825 435975334968055116447644869)
            ·
              refine ⟨81745375306510334333933413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 435975334968055116447644869 81745375306510334333933413)
              ·
                refine ⟨15327257869970687687612515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81745375306510334333933413 15327257869970687687612515)
                ·
                  refine ⟨22990886804956031531418773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15327257869970687687612515 22990886804956031531418773)
                  ·
                    refine ⟨1077697818982313978035255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22990886804956031531418773 1077697818982313978035255)
                    ·
                      rfl

theorem cell23_6296427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 6].length) (baseStart_6296427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296427 prefixEnd_6296427 := by exact prefixLift 6296427
  have htrace : WordTrace (prefixWord ++ tailWord_6296427) baseStart_6296427 baseEnd_6296427 := by
    simpa [prefixWord, tailWord_6296427, baseEnd_6296427] using wordTrace_append hprefix tailTrace_6296427
  have hstable : (prefixWord ++ tailWord_6296427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296427).length < 2 ^ (prefixWord ++ tailWord_6296427).sum := by decide
  have hdescent : baseEnd_6296427 < baseStart_6296427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296438 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6296438 : Nat := 118140960795 + 6296438 * 2 ^ 59
def prefixEnd_6296438 : Nat := 4983230072969 + 3 ^ 40 * 6296438 * 2
def baseEnd_6296438 : Nat := 3233099105234141391068215

theorem tailTrace_6296438 : CollatzResearch.WordTrace tailWord_6296438 prefixEnd_6296438 3233099105234141391068215 := by
  unfold tailWord_6296438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353122522692996677677623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153099973575391964561894645 14353122522692996677677623)
  ·
    refine ⟨21529683784039495016516435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14353122522692996677677623 21529683784039495016516435)
    ·
      refine ⟨32294525676059242524774653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21529683784039495016516435 32294525676059242524774653)
      ·
        refine ⟨12110447128522215946790495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32294525676059242524774653 12110447128522215946790495)
        ·
          refine ⟨18165670692783323920185743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12110447128522215946790495 18165670692783323920185743)
          ·
            refine ⟨27248506039174985880278615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18165670692783323920185743 27248506039174985880278615)
            ·
              refine ⟨40872759058762478820417923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27248506039174985880278615 40872759058762478820417923)
              ·
                refine ⟨61309138588143718230626885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40872759058762478820417923 61309138588143718230626885)
                ·
                  refine ⟨11495463485276947168242541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61309138588143718230626885 11495463485276947168242541)
                  ·
                    refine ⟨4310798806978855188090953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11495463485276947168242541 4310798806978855188090953)
                    ·
                      refine ⟨3233099105234141391068215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310798806978855188090953 3233099105234141391068215)
                      ·
                        rfl

theorem cell23_6296438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6296438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296438 prefixEnd_6296438 := by exact prefixLift 6296438
  have htrace : WordTrace (prefixWord ++ tailWord_6296438) baseStart_6296438 baseEnd_6296438 := by
    simpa [prefixWord, tailWord_6296438, baseEnd_6296438] using wordTrace_append hprefix tailTrace_6296438
  have hstable : (prefixWord ++ tailWord_6296438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296438).length < 2 ^ (prefixWord ++ tailWord_6296438).sum := by decide
  have hdescent : baseEnd_6296438 < baseStart_6296438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296447 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_6296447 : Nat := 118140960795 + 6296447 * 2 ^ 59
def prefixEnd_6296447 : Nat := 4983230072969 + 3 ^ 40 * 6296447 * 2
def baseEnd_6296447 : Nat := 3233103726560031855855673

theorem tailTrace_6296447 : CollatzResearch.WordTrace tailWord_6296447 prefixEnd_6296447 3233103726560031855855673 := by
  unfold tailWord_6296447
  simp only [CollatzResearch.WordTrace]
  refine ⟨229650288620055341379919595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153100192413370227586613063 229650288620055341379919595)
  ·
    refine ⟨344475432930083012069879393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229650288620055341379919595 344475432930083012069879393)
    ·
      refine ⟨258356574697562259052409545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344475432930083012069879393 258356574697562259052409545)
      ·
        refine ⟨193767431023171694289307159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258356574697562259052409545 193767431023171694289307159)
        ·
          refine ⟨290651146534757541433960739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193767431023171694289307159 290651146534757541433960739)
          ·
            refine ⟨435976719802136312150941109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290651146534757541433960739 435976719802136312150941109)
            ·
              refine ⟨40872817481450279264150729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435976719802136312150941109 40872817481450279264150729)
              ·
                refine ⟨30654613111087709448113047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40872817481450279264150729 30654613111087709448113047)
                ·
                  refine ⟨45981919666631564172169571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30654613111087709448113047 45981919666631564172169571)
                  ·
                    refine ⟨68972879499947346258254357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45981919666631564172169571 68972879499947346258254357)
                    ·
                      refine ⟨3233103726560031855855673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68972879499947346258254357 3233103726560031855855673)
                      ·
                        rfl

theorem cell23_6296447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_6296447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296447 prefixEnd_6296447 := by exact prefixLift 6296447
  have htrace : WordTrace (prefixWord ++ tailWord_6296447) baseStart_6296447 baseEnd_6296447 := by
    simpa [prefixWord, tailWord_6296447, baseEnd_6296447] using wordTrace_append hprefix tailTrace_6296447
  have hstable : (prefixWord ++ tailWord_6296447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296447).length < 2 ^ (prefixWord ++ tailWord_6296447).sum := by decide
  have hdescent : baseEnd_6296447 < baseStart_6296447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296457 : List Nat := [1, 2, 1, 1, 5, 2, 1, 10]
def baseStart_6296457 : Nat := 118140960795 + 6296457 * 2 ^ 59
def prefixEnd_6296457 : Nat := 4983230072969 + 3 ^ 40 * 6296457 * 2
def baseEnd_6296457 : Nat := 119744772643206548767801

theorem tailTrace_6296457 : CollatzResearch.WordTrace tailWord_6296457 prefixEnd_6296457 119744772643206548767801 := by
  unfold tailWord_6296457
  simp only [CollatzResearch.WordTrace]
  refine ⟨229650653350019113087783625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153100435566679408725189083 229650653350019113087783625)
  ·
    refine ⟨172237990012514334815837719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229650653350019113087783625 172237990012514334815837719)
    ·
      refine ⟨258356985018771502223756579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172237990012514334815837719 258356985018771502223756579)
      ·
        refine ⟨387535477528157253335634869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258356985018771502223756579 387535477528157253335634869)
        ·
          refine ⟨36331451018264742500215769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 387535477528157253335634869 36331451018264742500215769)
          ·
            refine ⟨27248588263698556875161827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36331451018264742500215769 27248588263698556875161827)
            ·
              refine ⟨40872882395547835312742741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27248588263698556875161827 40872882395547835312742741)
              ·
                refine ⟨119744772643206548767801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40872882395547835312742741 119744772643206548767801)
                ·
                  rfl

theorem cell23_6296457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 10].length) (baseStart_6296457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296457 prefixEnd_6296457 := by exact prefixLift 6296457
  have htrace : WordTrace (prefixWord ++ tailWord_6296457) baseStart_6296457 baseEnd_6296457 := by
    simpa [prefixWord, tailWord_6296457, baseEnd_6296457] using wordTrace_append hprefix tailTrace_6296457
  have hstable : (prefixWord ++ tailWord_6296457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296457).length < 2 ^ (prefixWord ++ tailWord_6296457).sum := by decide
  have hdescent : baseEnd_6296457 < baseStart_6296457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296468 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6296468 : Nat := 118140960795 + 6296468 * 2 ^ 59
def prefixEnd_6296468 : Nat := 4983230072969 + 3 ^ 40 * 6296468 * 2
def baseEnd_6296468 : Nat := 3233114509653776273693077

theorem tailTrace_6296468 : CollatzResearch.WordTrace tailWord_6296468 prefixEnd_6296468 3233114509653776273693077 := by
  unfold tailWord_6296468
  simp only [CollatzResearch.WordTrace]
  refine ⟨114825527276489630983217029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153100703035319507977622705 114825527276489630983217029)
  ·
    refine ⟨21529786364341805809353193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114825527276489630983217029 21529786364341805809353193)
    ·
      refine ⟨16147339773256354357014895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21529786364341805809353193 16147339773256354357014895)
      ·
        refine ⟨24221009659884531535522343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16147339773256354357014895 24221009659884531535522343)
        ·
          refine ⟨36331514489826797303283515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24221009659884531535522343 36331514489826797303283515)
          ·
            refine ⟨54497271734740195954925273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36331514489826797303283515 54497271734740195954925273)
            ·
              refine ⟨40872953801055146966193955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54497271734740195954925273 40872953801055146966193955)
              ·
                refine ⟨61309430701582720449290933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40872953801055146966193955 61309430701582720449290933)
                ·
                  refine ⟨5747759128273380042121025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61309430701582720449290933 5747759128273380042121025)
                  ·
                    refine ⟨4310819346205035031590769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5747759128273380042121025 4310819346205035031590769)
                    ·
                      refine ⟨3233114509653776273693077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310819346205035031590769 3233114509653776273693077)
                      ·
                        rfl

theorem cell23_6296468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6296468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296468 prefixEnd_6296468 := by exact prefixLift 6296468
  have htrace : WordTrace (prefixWord ++ tailWord_6296468) baseStart_6296468 baseEnd_6296468 := by
    simpa [prefixWord, tailWord_6296468, baseEnd_6296468] using wordTrace_append hprefix tailTrace_6296468
  have hstable : (prefixWord ++ tailWord_6296468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296468).length < 2 ^ (prefixWord ++ tailWord_6296468).sum := by decide
  have hdescent : baseEnd_6296468 < baseStart_6296468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296481 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6296481 : Nat := 118140960795 + 6296481 * 2 ^ 59
def prefixEnd_6296481 : Nat := 4983230072969 + 3 ^ 40 * 6296481 * 2
def baseEnd_6296481 : Nat := 3233121184902284722830517

theorem tailTrace_6296481 : CollatzResearch.WordTrace tailWord_6296481 prefixEnd_6296481 3233121184902284722830517 := by
  unfold tailWord_6296481
  simp only [CollatzResearch.WordTrace]
  refine ⟨229651528701932165186657297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153101019134621443457771531 229651528701932165186657297)
  ·
    refine ⟨172238646526449123889992973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229651528701932165186657297 172238646526449123889992973)
    ·
      refine ⟨64589492447418421458747365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172238646526449123889992973 64589492447418421458747365)
      ·
        refine ⟨12110529833890954023515131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64589492447418421458747365 12110529833890954023515131)
        ·
          refine ⟨18165794750836431035272697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12110529833890954023515131 18165794750836431035272697)
          ·
            refine ⟨13624346063127323276454523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18165794750836431035272697 13624346063127323276454523)
            ·
              refine ⟨20436519094690984914681785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13624346063127323276454523 20436519094690984914681785)
              ·
                refine ⟨15327389321018238686011339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20436519094690984914681785 15327389321018238686011339)
                ·
                  refine ⟨22991083981527358029017009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15327389321018238686011339 22991083981527358029017009)
                  ·
                    refine ⟨17243312986145518521762757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22991083981527358029017009 17243312986145518521762757)
                    ·
                      refine ⟨3233121184902284722830517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17243312986145518521762757 3233121184902284722830517)
                      ·
                        rfl

theorem cell23_6296481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6296481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296481 prefixEnd_6296481 := by exact prefixLift 6296481
  have htrace : WordTrace (prefixWord ++ tailWord_6296481) baseStart_6296481 baseEnd_6296481 := by
    simpa [prefixWord, tailWord_6296481, baseEnd_6296481] using wordTrace_append hprefix tailTrace_6296481
  have hstable : (prefixWord ++ tailWord_6296481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296481).length < 2 ^ (prefixWord ++ tailWord_6296481).sum := by decide
  have hdescent : baseEnd_6296481 < baseStart_6296481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296524 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6296524 : Nat := 118140960795 + 6296524 * 2 ^ 59
def prefixEnd_6296524 : Nat := 4983230072969 + 3 ^ 40 * 6296524 * 2
def baseEnd_6296524 : Nat := 3233143264570428054592819

theorem tailTrace_6296524 : CollatzResearch.WordTrace tailWord_6296524 prefixEnd_6296524 3233143264570428054592819 := by
  unfold tailWord_6296524
  simp only [CollatzResearch.WordTrace]
  refine ⟨114826548520388191765236313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153102064693850922353648417 114826548520388191765236313)
  ·
    refine ⟨86119911390291143823927235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114826548520388191765236313 86119911390291143823927235)
    ·
      refine ⟨129179867085436715735890853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86119911390291143823927235 129179867085436715735890853)
      ·
        refine ⟨24221225078519384200479535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129179867085436715735890853 24221225078519384200479535)
        ·
          refine ⟨36331837617779076300719303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24221225078519384200479535 36331837617779076300719303)
          ·
            refine ⟨54497756426668614451078955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36331837617779076300719303 54497756426668614451078955)
            ·
              refine ⟨81746634640002921676618433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54497756426668614451078955 81746634640002921676618433)
              ·
                refine ⟨61309975980002191257463825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81746634640002921676618433 61309975980002191257463825)
                ·
                  refine ⟨45982481985001643443097869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61309975980002191257463825 45982481985001643443097869)
                  ·
                    refine ⟨17243430744375616291161701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45982481985001643443097869 17243430744375616291161701)
                    ·
                      refine ⟨3233143264570428054592819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17243430744375616291161701 3233143264570428054592819)
                      ·
                        rfl

theorem cell23_6296524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6296524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296524 prefixEnd_6296524 := by exact prefixLift 6296524
  have htrace : WordTrace (prefixWord ++ tailWord_6296524) baseStart_6296524 baseEnd_6296524 := by
    simpa [prefixWord, tailWord_6296524, baseEnd_6296524] using wordTrace_append hprefix tailTrace_6296524
  have hstable : (prefixWord ++ tailWord_6296524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296524).length < 2 ^ (prefixWord ++ tailWord_6296524).sum := by decide
  have hdescent : baseEnd_6296524 < baseStart_6296524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296611 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 2, 5]
def baseStart_6296611 : Nat := 118140960795 + 6296611 * 2 ^ 59
def prefixEnd_6296611 : Nat := 4983230072969 + 3 ^ 40 * 6296611 * 2
def baseEnd_6296611 : Nat := 1077729312462456404734973

theorem tailTrace_6296611 : CollatzResearch.WordTrace tailWord_6296611 prefixEnd_6296611 1077729312462456404734973 := by
  unfold tailWord_6296611
  simp only [CollatzResearch.WordTrace]
  refine ⟨229656270191461197388889687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153104180127640798259259791 229656270191461197388889687)
  ·
    refine ⟨344484405287191796083334531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229656270191461197388889687 344484405287191796083334531)
    ·
      refine ⟨516726607930787694125001797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344484405287191796083334531 516726607930787694125001797)
      ·
        refine ⟨96886238987022692648437837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516726607930787694125001797 96886238987022692648437837)
        ·
          refine ⟨36332339620133509743164189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96886238987022692648437837 36332339620133509743164189)
          ·
            refine ⟨13624627357550066153686571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36332339620133509743164189 13624627357550066153686571)
            ·
              refine ⟨20436941036325099230529857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13624627357550066153686571 20436941036325099230529857)
              ·
                refine ⟨15327705777243824422897393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20436941036325099230529857 15327705777243824422897393)
                ·
                  refine ⟨11495779332932868317173045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15327705777243824422897393 11495779332932868317173045)
                  ·
                    refine ⟨1077729312462456404734973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11495779332932868317173045 1077729312462456404734973)
                    ·
                      rfl

theorem cell23_6296611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 5].length) (baseStart_6296611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296611 prefixEnd_6296611 := by exact prefixLift 6296611
  have htrace : WordTrace (prefixWord ++ tailWord_6296611) baseStart_6296611 baseEnd_6296611 := by
    simpa [prefixWord, tailWord_6296611, baseEnd_6296611] using wordTrace_append hprefix tailTrace_6296611
  have hstable : (prefixWord ++ tailWord_6296611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296611).length < 2 ^ (prefixWord ++ tailWord_6296611).sum := by decide
  have hdescent : baseEnd_6296611 < baseStart_6296611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296631 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_6296631 : Nat := 118140960795 + 6296631 * 2 ^ 59
def prefixEnd_6296631 : Nat := 4983230072969 + 3 ^ 40 * 6296631 * 2
def baseEnd_6296631 : Nat := 3233198207000459135954827

theorem tailTrace_6296631 : CollatzResearch.WordTrace tailWord_6296631 prefixEnd_6296631 3233198207000459135954827 := by
  unfold tailWord_6296631
  simp only [CollatzResearch.WordTrace]
  refine ⟨229656999651388740804617747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153104666434259160536411831 229656999651388740804617747)
  ·
    refine ⟨344485499477083111206926621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229656999651388740804617747 344485499477083111206926621)
    ·
      refine ⟨129182062303906166702597483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344485499477083111206926621 129182062303906166702597483)
      ·
        refine ⟨193773093455859250053896225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129182062303906166702597483 193773093455859250053896225)
        ·
          refine ⟨145329820091894437540422169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193773093455859250053896225 145329820091894437540422169)
          ·
            refine ⟨108997365068920828155316627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145329820091894437540422169 108997365068920828155316627)
            ·
              refine ⟨163496047603381242232974941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108997365068920828155316627 163496047603381242232974941)
              ·
                refine ⟨61311017851267965837365603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163496047603381242232974941 61311017851267965837365603)
                ·
                  refine ⟨91966526776901948756048405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61311017851267965837365603 91966526776901948756048405)
                  ·
                    refine ⟨4310930942667278847939769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91966526776901948756048405 4310930942667278847939769)
                    ·
                      refine ⟨3233198207000459135954827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4310930942667278847939769 3233198207000459135954827)
                      ·
                        rfl

theorem cell23_6296631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_6296631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296631 prefixEnd_6296631 := by exact prefixLift 6296631
  have htrace : WordTrace (prefixWord ++ tailWord_6296631) baseStart_6296631 baseEnd_6296631 := by
    simpa [prefixWord, tailWord_6296631, baseEnd_6296631] using wordTrace_append hprefix tailTrace_6296631
  have hstable : (prefixWord ++ tailWord_6296631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296631).length < 2 ^ (prefixWord ++ tailWord_6296631).sum := by decide
  have hdescent : baseEnd_6296631 < baseStart_6296631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296668 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_6296668 : Nat := 118140960795 + 6296668 * 2 ^ 59
def prefixEnd_6296668 : Nat := 4983230072969 + 3 ^ 40 * 6296668 * 2
def baseEnd_6296668 : Nat := 3233217205784675491192157

theorem tailTrace_6296668 : CollatzResearch.WordTrace tailWord_6296668 prefixEnd_6296668 3233217205784675491192157 := by
  unfold tailWord_6296668
  simp only [CollatzResearch.WordTrace]
  refine ⟨114829174576127348061857329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153105566101503130749143105 114829174576127348061857329)
  ·
    refine ⟨86121880932095511046392997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114829174576127348061857329 86121880932095511046392997)
    ·
      refine ⟨16147852674767908321198687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86121880932095511046392997 16147852674767908321198687)
      ·
        refine ⟨24221779012151862481798031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16147852674767908321198687 24221779012151862481798031)
        ·
          refine ⟨36332668518227793722697047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24221779012151862481798031 36332668518227793722697047)
          ·
            refine ⟨54499002777341690584045571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36332668518227793722697047 54499002777341690584045571)
            ·
              refine ⟨81748504166012535876068357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54499002777341690584045571 81748504166012535876068357)
              ·
                refine ⟨15327844531127350476762817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81748504166012535876068357 15327844531127350476762817)
                ·
                  refine ⟨11495883398345512857572113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15327844531127350476762817 11495883398345512857572113)
                  ·
                    refine ⟨8621912548759134643179085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11495883398345512857572113 8621912548759134643179085)
                    ·
                      refine ⟨3233217205784675491192157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8621912548759134643179085 3233217205784675491192157)
                      ·
                        rfl

theorem cell23_6296668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_6296668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296668 prefixEnd_6296668 := by exact prefixLift 6296668
  have htrace : WordTrace (prefixWord ++ tailWord_6296668) baseStart_6296668 baseEnd_6296668 := by
    simpa [prefixWord, tailWord_6296668, baseEnd_6296668] using wordTrace_append hprefix tailTrace_6296668
  have hstable : (prefixWord ++ tailWord_6296668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296668).length < 2 ^ (prefixWord ++ tailWord_6296668).sum := by decide
  have hdescent : baseEnd_6296668 < baseStart_6296668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296671 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 6]
def baseStart_6296671 : Nat := 118140960795 + 6296671 * 2 ^ 59
def prefixEnd_6296671 : Nat := 4983230072969 + 3 ^ 40 * 6296671 * 2
def baseEnd_6296671 : Nat := 359246527358515442161627

theorem tailTrace_6296671 : CollatzResearch.WordTrace tailWord_6296671 prefixEnd_6296671 359246527358515442161627 := by
  unfold tailWord_6296671
  simp only [CollatzResearch.WordTrace]
  refine ⟨229658458571243827636073867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153105639047495885090715911 229658458571243827636073867)
  ·
    refine ⟨344487687856865741454110801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229658458571243827636073867 344487687856865741454110801)
    ·
      refine ⟨258365765892649306090583101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344487687856865741454110801 258365765892649306090583101)
      ·
        refine ⟨96887162209743489783968663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258365765892649306090583101 96887162209743489783968663)
        ·
          refine ⟨145330743314615234675952995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96887162209743489783968663 145330743314615234675952995)
          ·
            refine ⟨217996114971922852013929493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145330743314615234675952995 217996114971922852013929493)
            ·
              refine ⟨10218567889308883688152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217996114971922852013929493 10218567889308883688152945)
              ·
                refine ⟨7663925916981662766114709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10218567889308883688152945 7663925916981662766114709)
                ·
                  refine ⟨359246527358515442161627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7663925916981662766114709 359246527358515442161627)
                  ·
                    rfl

theorem cell23_6296671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 6].length) (baseStart_6296671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296671 prefixEnd_6296671 := by exact prefixLift 6296671
  have htrace : WordTrace (prefixWord ++ tailWord_6296671) baseStart_6296671 baseEnd_6296671 := by
    simpa [prefixWord, tailWord_6296671, baseEnd_6296671] using wordTrace_append hprefix tailTrace_6296671
  have hstable : (prefixWord ++ tailWord_6296671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296671).length < 2 ^ (prefixWord ++ tailWord_6296671).sum := by decide
  have hdescent : baseEnd_6296671 < baseStart_6296671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296701 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_6296701 : Nat := 118140960795 + 6296701 * 2 ^ 59
def prefixEnd_6296701 : Nat := 4983230072969 + 3 ^ 40 * 6296701 * 2
def baseEnd_6296701 : Nat := 1077744716882091287359835

theorem tailTrace_6296701 : CollatzResearch.WordTrace tailWord_6296701 prefixEnd_6296701 1077744716882091287359835 := by
  unfold tailWord_6296701
  simp only [CollatzResearch.WordTrace]
  refine ⟨229659552761135142759665957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153106368507423428506443971 229659552761135142759665957)
  ·
    refine ⟨43061166142712839267437367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229659552761135142759665957 43061166142712839267437367)
    ·
      refine ⟨64591749214069258901156051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43061166142712839267437367 64591749214069258901156051)
      ·
        refine ⟨96887623821103888351734077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64591749214069258901156051 96887623821103888351734077)
        ·
          refine ⟨36332858932913958131900279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96887623821103888351734077 36332858932913958131900279)
          ·
            refine ⟨54499288399370937197850419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36332858932913958131900279 54499288399370937197850419)
            ·
              refine ⟨81748932599056405796775629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54499288399370937197850419 81748932599056405796775629)
              ·
                refine ⟨30655849724646152173790861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81748932599056405796775629 30655849724646152173790861)
                ·
                  refine ⟨11495943646742307065171573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30655849724646152173790861 11495943646742307065171573)
                  ·
                    refine ⟨1077744716882091287359835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11495943646742307065171573 1077744716882091287359835)
                    ·
                      rfl

theorem cell23_6296701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_6296701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296701 prefixEnd_6296701 := by exact prefixLift 6296701
  have htrace : WordTrace (prefixWord ++ tailWord_6296701) baseStart_6296701 baseEnd_6296701 := by
    simpa [prefixWord, tailWord_6296701, baseEnd_6296701] using wordTrace_append hprefix tailTrace_6296701
  have hstable : (prefixWord ++ tailWord_6296701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296701).length < 2 ^ (prefixWord ++ tailWord_6296701).sum := by decide
  have hdescent : baseEnd_6296701 < baseStart_6296701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296732 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6296732 : Nat := 118140960795 + 6296732 * 2 ^ 59
def prefixEnd_6296732 : Nat := 4983230072969 + 3 ^ 40 * 6296732 * 2
def baseEnd_6296732 : Nat := 3233250068546563240791863

theorem tailTrace_6296732 : CollatzResearch.WordTrace tailWord_6296732 prefixEnd_6296732 3233250068546563240791863 := by
  unfold tailWord_6296732
  simp only [CollatzResearch.WordTrace]
  refine ⟨114830341712011417527022225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153107122282681890036029633 114830341712011417527022225)
  ·
    refine ⟨86122756284008563145266669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114830341712011417527022225 86122756284008563145266669)
    ·
      refine ⟨32296033606503211179475001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86122756284008563145266669 32296033606503211179475001)
      ·
        refine ⟨24222025204877408384606251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32296033606503211179475001 24222025204877408384606251)
        ·
          refine ⟨36333037807316112576909377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24222025204877408384606251 36333037807316112576909377)
          ·
            refine ⟨27249778355487084432682033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36333037807316112576909377 27249778355487084432682033)
            ·
              refine ⟨20437333766615313324511525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27249778355487084432682033 20437333766615313324511525)
              ·
                refine ⟨3832000081240371248345911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20437333766615313324511525 3832000081240371248345911)
                ·
                  refine ⟨5748000121860556872518867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832000081240371248345911 5748000121860556872518867)
                  ·
                    refine ⟨8622000182790835308778301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5748000121860556872518867 8622000182790835308778301)
                    ·
                      refine ⟨3233250068546563240791863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8622000182790835308778301 3233250068546563240791863)
                      ·
                        rfl

theorem cell23_6296732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6296732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296732 prefixEnd_6296732 := by exact prefixLift 6296732
  have htrace : WordTrace (prefixWord ++ tailWord_6296732) baseStart_6296732 baseEnd_6296732 := by
    simpa [prefixWord, tailWord_6296732, baseEnd_6296732] using wordTrace_append hprefix tailTrace_6296732
  have hstable : (prefixWord ++ tailWord_6296732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296732).length < 2 ^ (prefixWord ++ tailWord_6296732).sum := by decide
  have hdescent : baseEnd_6296732 < baseStart_6296732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296741 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_6296741 : Nat := 118140960795 + 6296741 * 2 ^ 59
def prefixEnd_6296741 : Nat := 4983230072969 + 3 ^ 40 * 6296741 * 2
def baseEnd_6296741 : Nat := 3233254689872453705579321

theorem tailTrace_6296741 : CollatzResearch.WordTrace tailWord_6296741 prefixEnd_6296741 3233254689872453705579321 := by
  unfold tailWord_6296741
  simp only [CollatzResearch.WordTrace]
  refine ⟨229661011680990229591122077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153107341120660153060748051 229661011680990229591122077)
  ·
    refine ⟨86122879380371336096670779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229661011680990229591122077 86122879380371336096670779)
    ·
      refine ⟨129184319070557004145006169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86122879380371336096670779 129184319070557004145006169)
      ·
        refine ⟨96888239302917753108754627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129184319070557004145006169 96888239302917753108754627)
        ·
          refine ⟨145332358954376629663131941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96888239302917753108754627 145332358954376629663131941)
          ·
            refine ⟨27249817303945618061837239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145332358954376629663131941 27249817303945618061837239)
            ·
              refine ⟨40874725955918427092755859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27249817303945618061837239 40874725955918427092755859)
              ·
                refine ⟨61312088933877640639133789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40874725955918427092755859 61312088933877640639133789)
                ·
                  refine ⟨22992033350204115239675171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61312088933877640639133789 22992033350204115239675171)
                  ·
                    refine ⟨34488050025306172859512757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22992033350204115239675171 34488050025306172859512757)
                    ·
                      refine ⟨3233254689872453705579321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34488050025306172859512757 3233254689872453705579321)
                      ·
                        rfl

theorem cell23_6296741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_6296741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296741 prefixEnd_6296741 := by exact prefixLift 6296741
  have htrace : WordTrace (prefixWord ++ tailWord_6296741) baseStart_6296741 baseEnd_6296741 := by
    simpa [prefixWord, tailWord_6296741, baseEnd_6296741] using wordTrace_append hprefix tailTrace_6296741
  have hstable : (prefixWord ++ tailWord_6296741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296741).length < 2 ^ (prefixWord ++ tailWord_6296741).sum := by decide
  have hdescent : baseEnd_6296741 < baseStart_6296741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296755 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 3, 2, 2]
def baseStart_6296755 : Nat := 118140960795 + 6296755 * 2 ^ 59
def prefixEnd_6296755 : Nat := 4983230072969 + 3 ^ 40 * 6296755 * 2
def baseEnd_6296755 : Nat := 3233261878601616650804257

theorem tailTrace_6296755 : CollatzResearch.WordTrace tailWord_6296755 prefixEnd_6296755 3233261878601616650804257 := by
  unfold tailWord_6296755
  simp only [CollatzResearch.WordTrace]
  refine ⟨229661522302939509982131719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153107681535293006654754479 229661522302939509982131719)
  ·
    refine ⟨344492283454409264973197579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229661522302939509982131719 344492283454409264973197579)
    ·
      refine ⟨516738425181613897459796369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344492283454409264973197579 516738425181613897459796369)
      ·
        refine ⟨387553818886210423094847277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516738425181613897459796369 387553818886210423094847277)
        ·
          refine ⟨145332682082328908660567729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387553818886210423094847277 145332682082328908660567729)
          ·
            refine ⟨108999511561746681495425797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145332682082328908660567729 108999511561746681495425797)
            ·
              refine ⟨20437408417827502780392337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108999511561746681495425797 20437408417827502780392337)
              ·
                refine ⟨15328056313370627085294253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20437408417827502780392337 15328056313370627085294253)
                ·
                  refine ⟨5748021117513985156985345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15328056313370627085294253 5748021117513985156985345)
                  ·
                    refine ⟨4311015838135488867739009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748021117513985156985345 4311015838135488867739009)
                    ·
                      refine ⟨3233261878601616650804257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311015838135488867739009 3233261878601616650804257)
                      ·
                        rfl

theorem cell23_6296755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2, 2].length) (baseStart_6296755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296755 prefixEnd_6296755 := by exact prefixLift 6296755
  have htrace : WordTrace (prefixWord ++ tailWord_6296755) baseStart_6296755 baseEnd_6296755 := by
    simpa [prefixWord, tailWord_6296755, baseEnd_6296755] using wordTrace_append hprefix tailTrace_6296755
  have hstable : (prefixWord ++ tailWord_6296755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296755).length < 2 ^ (prefixWord ++ tailWord_6296755).sum := by decide
  have hdescent : baseEnd_6296755 < baseStart_6296755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296761 : List Nat := [1, 2, 1, 4, 1, 4, 1, 9]
def baseStart_6296761 : Nat := 118140960795 + 6296761 * 2 ^ 59
def prefixEnd_6296761 : Nat := 4983230072969 + 3 ^ 40 * 6296761 * 2
def baseEnd_6296761 : Nat := 119750554055020134345527

theorem tailTrace_6296761 : CollatzResearch.WordTrace tailWord_6296761 prefixEnd_6296761 119750554055020134345527 := by
  unfold tailWord_6296761
  simp only [CollatzResearch.WordTrace]
  refine ⟨229661741140917773006850137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153107827427278515337900091 229661741140917773006850137)
  ·
    refine ⟨172246305855688329755137603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229661741140917773006850137 172246305855688329755137603)
    ·
      refine ⟨258369458783532494632706405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172246305855688329755137603 258369458783532494632706405)
      ·
        refine ⟨48444273521912342743632451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258369458783532494632706405 48444273521912342743632451)
        ·
          refine ⟨72666410282868514115448677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48444273521912342743632451 72666410282868514115448677)
          ·
            refine ⟨13624951928037846396646627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72666410282868514115448677 13624951928037846396646627)
            ·
              refine ⟨20437427892056769594969941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13624951928037846396646627 20437427892056769594969941)
              ·
                refine ⟨119750554055020134345527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20437427892056769594969941 119750554055020134345527)
                ·
                  rfl

theorem cell23_6296761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 9].length) (baseStart_6296761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296761 prefixEnd_6296761 := by exact prefixLift 6296761
  have htrace : WordTrace (prefixWord ++ tailWord_6296761) baseStart_6296761 baseEnd_6296761 := by
    simpa [prefixWord, tailWord_6296761, baseEnd_6296761] using wordTrace_append hprefix tailTrace_6296761
  have hstable : (prefixWord ++ tailWord_6296761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296761).length < 2 ^ (prefixWord ++ tailWord_6296761).sum := by decide
  have hdescent : baseEnd_6296761 < baseStart_6296761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296789 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6296789 : Nat := 118140960795 + 6296789 * 2 ^ 59
def prefixEnd_6296789 : Nat := 4983230072969 + 3 ^ 40 * 6296789 * 2
def baseEnd_6296789 : Nat := 3233279336943869517779101

theorem tailTrace_6296789 : CollatzResearch.WordTrace tailWord_6296789 prefixEnd_6296789 3233279336943869517779101 := by
  unfold tailWord_6296789
  simp only [CollatzResearch.WordTrace]
  refine ⟨229662762384816333788869421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153108508256544222525912947 229662762384816333788869421)
  ·
    refine ⟨86123535894306125170826033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229662762384816333788869421 86123535894306125170826033)
    ·
      refine ⟨64592651920729593878119525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86123535894306125170826033 64592651920729593878119525)
      ·
        refine ⟨12111122235136798852147411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64592651920729593878119525 12111122235136798852147411)
        ·
          refine ⟨18166683352705198278221117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12111122235136798852147411 18166683352705198278221117)
          ·
            refine ⟨6812506257264449354332919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18166683352705198278221117 6812506257264449354332919)
            ·
              refine ⟨10218759385896674031499379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812506257264449354332919 10218759385896674031499379)
              ·
                refine ⟨15328139078845011047249069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10218759385896674031499379 15328139078845011047249069)
                ·
                  refine ⟨5748052154566879142718401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15328139078845011047249069 5748052154566879142718401)
                  ·
                    refine ⟨4311039115925159357038801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748052154566879142718401 4311039115925159357038801)
                    ·
                      refine ⟨3233279336943869517779101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311039115925159357038801 3233279336943869517779101)
                      ·
                        rfl

theorem cell23_6296789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6296789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296789 prefixEnd_6296789 := by exact prefixLift 6296789
  have htrace : WordTrace (prefixWord ++ tailWord_6296789) baseStart_6296789 baseEnd_6296789 := by
    simpa [prefixWord, tailWord_6296789, baseEnd_6296789] using wordTrace_append hprefix tailTrace_6296789
  have hstable : (prefixWord ++ tailWord_6296789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296789).length < 2 ^ (prefixWord ++ tailWord_6296789).sum := by decide
  have hdescent : baseEnd_6296789 < baseStart_6296789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296858 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_6296858 : Nat := 118140960795 + 6296858 * 2 ^ 59
def prefixEnd_6296858 : Nat := 4983230072969 + 3 ^ 40 * 6296858 * 2
def baseEnd_6296858 : Nat := 3233314767109029747816283

theorem tailTrace_6296858 : CollatzResearch.WordTrace tailWord_6296858 prefixEnd_6296858 3233314767109029747816283 := by
  unfold tailWord_6296858
  simp only [CollatzResearch.WordTrace]
  refine ⟨57416319755391589643282807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153110186014377572382087485 57416319755391589643282807)
  ·
    refine ⟨86124479633087384464924211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57416319755391589643282807 86124479633087384464924211)
    ·
      refine ⟨129186719449631076697386317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86124479633087384464924211 129186719449631076697386317)
      ·
        refine ⟨48445019793611653761519869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129186719449631076697386317 48445019793611653761519869)
        ·
          refine ⟨18166882422604370160569951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48445019793611653761519869 18166882422604370160569951)
          ·
            refine ⟨27250323633906555240854927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18166882422604370160569951 27250323633906555240854927)
            ·
              refine ⟨40875485450859832861282391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27250323633906555240854927 40875485450859832861282391)
              ·
                refine ⟨61313228176289749291923587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40875485450859832861282391 61313228176289749291923587)
                ·
                  refine ⟨91969842264434623937885381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61313228176289749291923587 91969842264434623937885381)
                  ·
                    refine ⟨17244345424581491988353509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91969842264434623937885381 17244345424581491988353509)
                    ·
                      refine ⟨3233314767109029747816283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17244345424581491988353509 3233314767109029747816283)
                      ·
                        rfl

theorem cell23_6296858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_6296858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296858 prefixEnd_6296858 := by exact prefixLift 6296858
  have htrace : WordTrace (prefixWord ++ tailWord_6296858) baseStart_6296858 baseEnd_6296858 := by
    simpa [prefixWord, tailWord_6296858, baseEnd_6296858] using wordTrace_append hprefix tailTrace_6296858
  have hstable : (prefixWord ++ tailWord_6296858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296858).length < 2 ^ (prefixWord ++ tailWord_6296858).sum := by decide
  have hdescent : baseEnd_6296858 < baseStart_6296858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296868 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 7]
def baseStart_6296868 : Nat := 118140960795 + 6296868 * 2 ^ 59
def prefixEnd_6296868 : Nat := 4983230072969 + 3 ^ 40 * 6296868 * 2
def baseEnd_6296868 : Nat := 359257766879508300965693

theorem tailTrace_6296868 : CollatzResearch.WordTrace tailWord_6296868 prefixEnd_6296868 359257766879508300965693 := by
  unfold tailWord_6296868
  simp only [CollatzResearch.WordTrace]
  refine ⟨114832821875765065140497629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153110429167686753520663505 114832821875765065140497629)
  ·
    refine ⟨43062308203411899427686611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114832821875765065140497629 43062308203411899427686611)
    ·
      refine ⟨64593462305117849141529917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43062308203411899427686611 64593462305117849141529917)
      ·
        refine ⟨24222548364419193428073719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64593462305117849141529917 24222548364419193428073719)
        ·
          refine ⟨36333822546628790142110579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24222548364419193428073719 36333822546628790142110579)
          ·
            refine ⟨54500733819943185213165869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36333822546628790142110579 54500733819943185213165869)
            ·
              refine ⟨20437775182478694454937201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54500733819943185213165869 20437775182478694454937201)
              ·
                refine ⟨15328331386859020841202901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20437775182478694454937201 15328331386859020841202901)
                ·
                  refine ⟨359257766879508300965693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15328331386859020841202901 359257766879508300965693)
                  ·
                    rfl

theorem cell23_6296868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_6296868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296868 prefixEnd_6296868 := by exact prefixLift 6296868
  have htrace : WordTrace (prefixWord ++ tailWord_6296868) baseStart_6296868 baseEnd_6296868 := by
    simpa [prefixWord, tailWord_6296868, baseEnd_6296868] using wordTrace_append hprefix tailTrace_6296868
  have hstable : (prefixWord ++ tailWord_6296868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296868).length < 2 ^ (prefixWord ++ tailWord_6296868).sum := by decide
  have hdescent : baseEnd_6296868 < baseStart_6296868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296885 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 5]
def baseStart_6296885 : Nat := 118140960795 + 6296885 * 2 ^ 59
def prefixEnd_6296885 : Nat := 4983230072969 + 3 ^ 40 * 6296885 * 2
def baseEnd_6296885 : Nat := 359258736787411238019851

theorem tailTrace_6296885 : CollatzResearch.WordTrace tailWord_6296885 prefixEnd_6296885 359258736787411238019851 := by
  unfold tailWord_6296885
  simp only [CollatzResearch.WordTrace]
  refine ⟨229666263792468542184364109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153110842528312361456242739 229666263792468542184364109)
  ·
    refine ⟨86124848922175703319136541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229666263792468542184364109 86124848922175703319136541)
    ·
      refine ⟨32296818345815888744676203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86124848922175703319136541 32296818345815888744676203)
      ·
        refine ⟨48445227518723833117014305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32296818345815888744676203 48445227518723833117014305)
        ·
          refine ⟨36333920639042874837760729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48445227518723833117014305 36333920639042874837760729)
          ·
            refine ⟨27250440479282156128320547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36333920639042874837760729 27250440479282156128320547)
            ·
              refine ⟨40875660718923234192480821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27250440479282156128320547 40875660718923234192480821)
              ·
                refine ⟨3832093192399053205545077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40875660718923234192480821 3832093192399053205545077)
                ·
                  refine ⟨359258736787411238019851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3832093192399053205545077 359258736787411238019851)
                  ·
                    rfl

theorem cell23_6296885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_6296885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296885 prefixEnd_6296885 := by exact prefixLift 6296885
  have htrace : WordTrace (prefixWord ++ tailWord_6296885) baseStart_6296885 baseEnd_6296885 := by
    simpa [prefixWord, tailWord_6296885, baseEnd_6296885] using wordTrace_append hprefix tailTrace_6296885
  have hstable : (prefixWord ++ tailWord_6296885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296885).length < 2 ^ (prefixWord ++ tailWord_6296885).sum := by decide
  have hdescent : baseEnd_6296885 < baseStart_6296885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6296955 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3]
def baseStart_6296955 : Nat := 118140960795 + 6296955 * 2 ^ 59
def prefixEnd_6296955 : Nat := 4983230072969 + 3 ^ 40 * 6296955 * 2
def baseEnd_6296955 : Nat := 3233364574732515868303337

theorem tailTrace_6296955 : CollatzResearch.WordTrace tailWord_6296955 prefixEnd_6296955 3233364574732515868303337 := by
  unfold tailWord_6296955
  simp only [CollatzResearch.WordTrace]
  refine ⟨229668816902214944139412319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153112544601476629426274879 229668816902214944139412319)
  ·
    refine ⟨344503225353322416209118479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229668816902214944139412319 344503225353322416209118479)
    ·
      refine ⟨516754838029983624313677719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344503225353322416209118479 516754838029983624313677719)
      ·
        refine ⟨775132257044975436470516579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516754838029983624313677719 775132257044975436470516579)
        ·
          refine ⟨1162698385567463154705774869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775132257044975436470516579 1162698385567463154705774869)
          ·
            refine ⟨54501486823474835376833197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1162698385567463154705774869 54501486823474835376833197)
            ·
              refine ⟨20438057558803063266312449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54501486823474835376833197 20438057558803063266312449)
              ·
                refine ⟨15328543169102297449734337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20438057558803063266312449 15328543169102297449734337)
                ·
                  refine ⟨11496407376826723087300753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15328543169102297449734337 11496407376826723087300753)
                  ·
                    refine ⟨8622305532620042315475565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11496407376826723087300753 8622305532620042315475565)
                    ·
                      refine ⟨3233364574732515868303337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8622305532620042315475565 3233364574732515868303337)
                      ·
                        rfl

theorem cell23_6296955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 3].length) (baseStart_6296955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6296955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6296955 prefixEnd_6296955 := by exact prefixLift 6296955
  have htrace : WordTrace (prefixWord ++ tailWord_6296955) baseStart_6296955 baseEnd_6296955 := by
    simpa [prefixWord, tailWord_6296955, baseEnd_6296955] using wordTrace_append hprefix tailTrace_6296955
  have hstable : (prefixWord ++ tailWord_6296955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6296955).length < 2 ^ (prefixWord ++ tailWord_6296955).sum := by decide
  have hdescent : baseEnd_6296955 < baseStart_6296955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6296955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297046 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6297046 : Nat := 118140960795 + 6297046 * 2 ^ 59
def prefixEnd_6297046 : Nat := 4983230072969 + 3 ^ 40 * 6297046 * 2
def baseEnd_6297046 : Nat := 3233411301472075012265419

theorem tailTrace_6297046 : CollatzResearch.WordTrace tailWord_6297046 prefixEnd_6297046 3233411301472075012265419 := by
  unfold tailWord_6297046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14354508496555329167560937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153114757296590177787316661 14354508496555329167560937)
  ·
    refine ⟨10765881372416496875670703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14354508496555329167560937 10765881372416496875670703)
    ·
      refine ⟨16148822058624745313506055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10765881372416496875670703 16148822058624745313506055)
      ·
        refine ⟨24223233087937117970259083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16148822058624745313506055 24223233087937117970259083)
        ·
          refine ⟨36334849631905676955388625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24223233087937117970259083 36334849631905676955388625)
          ·
            refine ⟨27251137223929257716541469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36334849631905676955388625 27251137223929257716541469)
            ·
              refine ⟨10219176458973471643703051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27251137223929257716541469 10219176458973471643703051)
              ·
                refine ⟨15328764688460207465554577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219176458973471643703051 15328764688460207465554577)
                ·
                  refine ⟨11496573516345155599165933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15328764688460207465554577 11496573516345155599165933)
                  ·
                    refine ⟨4311215068629433349687225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11496573516345155599165933 4311215068629433349687225)
                    ·
                      refine ⟨3233411301472075012265419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311215068629433349687225 3233411301472075012265419)
                      ·
                        rfl

theorem cell23_6297046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6297046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297046 prefixEnd_6297046 := by exact prefixLift 6297046
  have htrace : WordTrace (prefixWord ++ tailWord_6297046) baseStart_6297046 baseEnd_6297046 := by
    simpa [prefixWord, tailWord_6297046, baseEnd_6297046] using wordTrace_append hprefix tailTrace_6297046
  have hstable : (prefixWord ++ tailWord_6297046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297046).length < 2 ^ (prefixWord ++ tailWord_6297046).sum := by decide
  have hdescent : baseEnd_6297046 < baseStart_6297046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297048 : List Nat := [2, 1, 2, 2, 2, 1, 2, 11]
def baseStart_6297048 : Nat := 118140960795 + 6297048 * 2 ^ 59
def prefixEnd_6297048 : Nat := 4983230072969 + 3 ^ 40 * 6297048 * 2
def baseEnd_6297048 : Nat := 119756012164199407571867

theorem tailTrace_6297048 : CollatzResearch.WordTrace tailWord_6297048 prefixEnd_6297048 119756012164199407571867 := by
  unfold tailWord_6297048
  simp only [CollatzResearch.WordTrace]
  refine ⟨114836104445439010511273899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153114805927252014015031865 114836104445439010511273899)
  ·
    refine ⟨172254156668158515766910849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114836104445439010511273899 172254156668158515766910849)
    ·
      refine ⟨129190617501118886825183137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172254156668158515766910849 129190617501118886825183137)
      ·
        refine ⟨96892963125839165118887353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129190617501118886825183137 96892963125839165118887353)
        ·
          refine ⟨72669722344379373839165515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96892963125839165118887353 72669722344379373839165515)
          ·
            refine ⟨109004583516569060758748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72669722344379373839165515 109004583516569060758748273)
            ·
              refine ⟨81753437637426795569061205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109004583516569060758748273 81753437637426795569061205)
              ·
                refine ⟨119756012164199407571867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81753437637426795569061205 119756012164199407571867)
                ·
                  rfl

theorem cell23_6297048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 11].length) (baseStart_6297048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297048 prefixEnd_6297048 := by exact prefixLift 6297048
  have htrace : WordTrace (prefixWord ++ tailWord_6297048) baseStart_6297048 baseEnd_6297048 := by
    simpa [prefixWord, tailWord_6297048, baseEnd_6297048] using wordTrace_append hprefix tailTrace_6297048
  have hstable : (prefixWord ++ tailWord_6297048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297048).length < 2 ^ (prefixWord ++ tailWord_6297048).sum := by decide
  have hdescent : baseEnd_6297048 < baseStart_6297048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297055 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_6297055 : Nat := 118140960795 + 6297055 * 2 ^ 59
def prefixEnd_6297055 : Nat := 4983230072969 + 3 ^ 40 * 6297055 * 2
def baseEnd_6297055 : Nat := 3233415922797965477052877

theorem tailTrace_6297055 : CollatzResearch.WordTrace tailWord_6297055 prefixEnd_6297055 3233415922797965477052877 := by
  unfold tailWord_6297055
  simp only [CollatzResearch.WordTrace]
  refine ⟨229672464201852661218052619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153114976134568440812035079 229672464201852661218052619)
  ·
    refine ⟨344508696302778991827078929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229672464201852661218052619 344508696302778991827078929)
    ·
      refine ⟨258381522227084243870309197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344508696302778991827078929 258381522227084243870309197)
      ·
        refine ⟨96893070835156591451365949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258381522227084243870309197 96893070835156591451365949)
        ·
          refine ⟨36334901563183721794262231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96893070835156591451365949 36334901563183721794262231)
          ·
            refine ⟨54502352344775582691393347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36334901563183721794262231 54502352344775582691393347)
            ·
              refine ⟨81753528517163374037090021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54502352344775582691393347 81753528517163374037090021)
              ·
                refine ⟨15328786596968132631954379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81753528517163374037090021 15328786596968132631954379)
                ·
                  refine ⟨22993179895452198947931569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15328786596968132631954379 22993179895452198947931569)
                  ·
                    refine ⟨17244884921589149210948677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22993179895452198947931569 17244884921589149210948677)
                    ·
                      refine ⟨3233415922797965477052877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17244884921589149210948677 3233415922797965477052877)
                      ·
                        rfl

theorem cell23_6297055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_6297055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297055 prefixEnd_6297055 := by exact prefixLift 6297055
  have htrace : WordTrace (prefixWord ++ tailWord_6297055) baseStart_6297055 baseEnd_6297055 := by
    simpa [prefixWord, tailWord_6297055, baseEnd_6297055] using wordTrace_append hprefix tailTrace_6297055
  have hstable : (prefixWord ++ tailWord_6297055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297055).length < 2 ^ (prefixWord ++ tailWord_6297055).sum := by decide
  have hdescent : baseEnd_6297055 < baseStart_6297055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297059 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 1, 1, 4]
def baseStart_6297059 : Nat := 118140960795 + 6297059 * 2 ^ 59
def prefixEnd_6297059 : Nat := 4983230072969 + 3 ^ 40 * 6297059 * 2
def baseEnd_6297059 : Nat := 3233417976720583461402859

theorem tailTrace_6297059 : CollatzResearch.WordTrace tailWord_6297059 prefixEnd_6297059 3233417976720583461402859 := by
  unfold tailWord_6297059
  simp only [CollatzResearch.WordTrace]
  refine ⟨229672610093838169901198231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153115073395892113267465487 229672610093838169901198231)
  ·
    refine ⟨344508915140757254851797347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229672610093838169901198231 344508915140757254851797347)
    ·
      refine ⟨516763372711135882277696021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344508915140757254851797347 516763372711135882277696021)
      ·
        refine ⟨24223283095834494481767001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 516763372711135882277696021 24223283095834494481767001)
        ·
          refine ⟨18167462321875870861325251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24223283095834494481767001 18167462321875870861325251)
          ·
            refine ⟨27251193482813806291987877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18167462321875870861325251 27251193482813806291987877)
            ·
              refine ⟨5109598778027588679747727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27251193482813806291987877 5109598778027588679747727)
              ·
                refine ⟨7664398167041383019621591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109598778027588679747727 7664398167041383019621591)
                ·
                  refine ⟨11496597250562074529432387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7664398167041383019621591 11496597250562074529432387)
                  ·
                    refine ⟨17244895875843111794148581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11496597250562074529432387 17244895875843111794148581)
                    ·
                      refine ⟨3233417976720583461402859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17244895875843111794148581 3233417976720583461402859)
                      ·
                        rfl

theorem cell23_6297059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_6297059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297059 prefixEnd_6297059 := by exact prefixLift 6297059
  have htrace : WordTrace (prefixWord ++ tailWord_6297059) baseStart_6297059 baseEnd_6297059 := by
    simpa [prefixWord, tailWord_6297059, baseEnd_6297059] using wordTrace_append hprefix tailTrace_6297059
  have hstable : (prefixWord ++ tailWord_6297059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297059).length < 2 ^ (prefixWord ++ tailWord_6297059).sum := by decide
  have hdescent : baseEnd_6297059 < baseStart_6297059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297069 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_6297069 : Nat := 118140960795 + 6297069 * 2 ^ 59
def prefixEnd_6297069 : Nat := 4983230072969 + 3 ^ 40 * 6297069 * 2
def baseEnd_6297069 : Nat := 1077807703842376140759271

theorem tailTrace_6297069 : CollatzResearch.WordTrace tailWord_6297069 prefixEnd_6297069 1077807703842376140759271 := by
  unfold tailWord_6297069
  simp only [CollatzResearch.WordTrace]
  refine ⟨229672974823801941609062261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153115316549201294406041507 229672974823801941609062261)
  ·
    refine ⟨21531841389731432025849587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229672974823801941609062261 21531841389731432025849587)
    ·
      refine ⟨32297762084597148038774381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21531841389731432025849587 32297762084597148038774381)
      ·
        refine ⟨12111660781723930514540393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32297762084597148038774381 12111660781723930514540393)
        ·
          refine ⟨9083745586292947885905295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12111660781723930514540393 9083745586292947885905295)
          ·
            refine ⟨13625618379439421828857943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083745586292947885905295 13625618379439421828857943)
            ·
              refine ⟨20438427569159132743286915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13625618379439421828857943 20438427569159132743286915)
              ·
                refine ⟨30657641353738699114930373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20438427569159132743286915 30657641353738699114930373)
                ·
                  refine ⟨5748307753826006084049445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30657641353738699114930373 5748307753826006084049445)
                  ·
                    refine ⟨1077807703842376140759271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748307753826006084049445 1077807703842376140759271)
                    ·
                      rfl

theorem cell23_6297069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_6297069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297069 prefixEnd_6297069 := by exact prefixLift 6297069
  have htrace : WordTrace (prefixWord ++ tailWord_6297069) baseStart_6297069 baseEnd_6297069 := by
    simpa [prefixWord, tailWord_6297069, baseEnd_6297069] using wordTrace_append hprefix tailTrace_6297069
  have hstable : (prefixWord ++ tailWord_6297069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297069).length < 2 ^ (prefixWord ++ tailWord_6297069).sum := by decide
  have hdescent : baseEnd_6297069 < baseStart_6297069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297086 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6297086 : Nat := 118140960795 + 6297086 * 2 ^ 59
def prefixEnd_6297086 : Nat := 4983230072969 + 3 ^ 40 * 6297086 * 2
def baseEnd_6297086 : Nat := 1077810613566084951921745

theorem tailTrace_6297086 : CollatzResearch.WordTrace tailWord_6297086 prefixEnd_6297086 1077810613566084951921745 := by
  unfold tailWord_6297086
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709199358092544189053889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153115729909826902341620741 28709199358092544189053889)
  ·
    refine ⟨21531899518569408141790417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28709199358092544189053889 21531899518569408141790417)
    ·
      refine ⟨16148924638927056106342813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21531899518569408141790417 16148924638927056106342813)
      ·
        refine ⟨6055846739597646039878555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16148924638927056106342813 6055846739597646039878555)
        ·
          refine ⟨9083770109396469059817833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055846739597646039878555 9083770109396469059817833)
          ·
            refine ⟨6812827582047351794863375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9083770109396469059817833 6812827582047351794863375)
            ·
              refine ⟨10219241373071027692295063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812827582047351794863375 10219241373071027692295063)
              ·
                refine ⟨15328862059606541538442595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219241373071027692295063 15328862059606541538442595)
                ·
                  refine ⟨22993293089409812307663893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15328862059606541538442595 22993293089409812307663893)
                  ·
                    refine ⟨1077810613566084951921745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22993293089409812307663893 1077810613566084951921745)
                    ·
                      rfl

theorem cell23_6297086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6297086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297086 prefixEnd_6297086 := by exact prefixLift 6297086
  have htrace : WordTrace (prefixWord ++ tailWord_6297086) baseStart_6297086 baseEnd_6297086 := by
    simpa [prefixWord, tailWord_6297086, baseEnd_6297086] using wordTrace_append hprefix tailTrace_6297086
  have hstable : (prefixWord ++ tailWord_6297086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297086).length < 2 ^ (prefixWord ++ tailWord_6297086).sum := by decide
  have hdescent : baseEnd_6297086 < baseStart_6297086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297089 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_6297089 : Nat := 118140960795 + 6297089 * 2 ^ 59
def prefixEnd_6297089 : Nat := 4983230072969 + 3 ^ 40 * 6297089 * 2
def baseEnd_6297089 : Nat := 3233433381140218344027721

theorem tailTrace_6297089 : CollatzResearch.WordTrace tailWord_6297089 prefixEnd_6297089 3233433381140218344027721 := by
  unfold tailWord_6297089
  simp only [CollatzResearch.WordTrace]
  refine ⟨229673704283729485024790321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153115802855819656683193547 229673704283729485024790321)
  ·
    refine ⟨172255278212797113768592741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229673704283729485024790321 172255278212797113768592741)
    ·
      refine ⟨32297864664899458831611139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172255278212797113768592741 32297864664899458831611139)
      ·
        refine ⟨48446796997349188247416709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32297864664899458831611139 48446796997349188247416709)
        ·
          refine ⟨9083774437002972796390633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48446796997349188247416709 9083774437002972796390633)
          ·
            refine ⟨6812830827752229597292975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9083774437002972796390633 6812830827752229597292975)
            ·
              refine ⟨10219246241628344395939463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812830827752229597292975 10219246241628344395939463)
              ·
                refine ⟨15328869362442516593909195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219246241628344395939463 15328869362442516593909195)
                ·
                  refine ⟨22993304043663774890863793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15328869362442516593909195 22993304043663774890863793)
                  ·
                    refine ⟨17244978032747831168147845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22993304043663774890863793 17244978032747831168147845)
                    ·
                      refine ⟨3233433381140218344027721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17244978032747831168147845 3233433381140218344027721)
                      ·
                        rfl

theorem cell23_6297089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_6297089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297089 prefixEnd_6297089 := by exact prefixLift 6297089
  have htrace : WordTrace (prefixWord ++ tailWord_6297089) baseStart_6297089 baseEnd_6297089 := by
    simpa [prefixWord, tailWord_6297089, baseEnd_6297089] using wordTrace_append hprefix tailTrace_6297089
  have hstable : (prefixWord ++ tailWord_6297089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297089).length < 2 ^ (prefixWord ++ tailWord_6297089).sum := by decide
  have hdescent : baseEnd_6297089 < baseStart_6297089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297099 : List Nat := [1, 1, 1, 1, 9, 1, 2, 7]
def baseStart_6297099 : Nat := 118140960795 + 6297099 * 2 ^ 59
def prefixEnd_6297099 : Nat := 4983230072969 + 3 ^ 40 * 6297099 * 2
def baseEnd_6297099 : Nat := 119756982072102344626025

theorem tailTrace_6297099 : CollatzResearch.WordTrace tailWord_6297099 prefixEnd_6297099 119756982072102344626025 := by
  unfold tailWord_6297099
  simp only [CollatzResearch.WordTrace]
  refine ⟨229674069013693256732654351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153116046009128837821769567 229674069013693256732654351)
  ·
    refine ⟨344511103520539885098981527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229674069013693256732654351 344511103520539885098981527)
    ·
      refine ⟨516766655280809827648472291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344511103520539885098981527 516766655280809827648472291)
      ·
        refine ⟨775149982921214741472708437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516766655280809827648472291 775149982921214741472708437)
        ·
          refine ⟨4541894431178992625816651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 775149982921214741472708437 4541894431178992625816651)
          ·
            refine ⟨6812841646768488938724977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541894431178992625816651 6812841646768488938724977)
            ·
              refine ⟨5109631235076366704043733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6812841646768488938724977 5109631235076366704043733)
              ·
                refine ⟨119756982072102344626025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5109631235076366704043733 119756982072102344626025)
                ·
                  rfl

theorem cell23_6297099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 7].length) (baseStart_6297099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297099 prefixEnd_6297099 := by exact prefixLift 6297099
  have htrace : WordTrace (prefixWord ++ tailWord_6297099) baseStart_6297099 baseEnd_6297099 := by
    simpa [prefixWord, tailWord_6297099, baseEnd_6297099] using wordTrace_append hprefix tailTrace_6297099
  have hstable : (prefixWord ++ tailWord_6297099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297099).length < 2 ^ (prefixWord ++ tailWord_6297099).sum := by decide
  have hdescent : baseEnd_6297099 < baseStart_6297099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297119 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 1, 3, 2]
def baseStart_6297119 : Nat := 118140960795 + 6297119 * 2 ^ 59
def prefixEnd_6297119 : Nat := 4983230072969 + 3 ^ 40 * 6297119 * 2
def baseEnd_6297119 : Nat := 3233448785559853226652583

theorem tailTrace_6297119 : CollatzResearch.WordTrace tailWord_6297119 prefixEnd_6297119 3233448785559853226652583 := by
  unfold tailWord_6297119
  simp only [CollatzResearch.WordTrace]
  refine ⟨229674798473620800148382411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153116532315747200098921607 229674798473620800148382411)
  ·
    refine ⟨344512197710431200222573617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229674798473620800148382411 344512197710431200222573617)
    ·
      refine ⟨258384148282823400166930213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344512197710431200222573617 258384148282823400166930213)
      ·
        refine ⟨48447027803029387531299415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258384148282823400166930213 48447027803029387531299415)
        ·
          refine ⟨72670541704544081296949123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48447027803029387531299415 72670541704544081296949123)
          ·
            refine ⟨109005812556816121945423685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72670541704544081296949123 109005812556816121945423685)
            ·
              refine ⟨20438589854403022864766941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109005812556816121945423685 20438589854403022864766941)
              ·
                refine ⟨7664471195401133574287603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20438589854403022864766941 7664471195401133574287603)
                ·
                  refine ⟨11496706793101700361431405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7664471195401133574287603 11496706793101700361431405)
                  ·
                    refine ⟨4311265047413137635536777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11496706793101700361431405 4311265047413137635536777)
                    ·
                      refine ⟨3233448785559853226652583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311265047413137635536777 3233448785559853226652583)
                      ·
                        rfl

theorem cell23_6297119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_6297119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297119 prefixEnd_6297119 := by exact prefixLift 6297119
  have htrace : WordTrace (prefixWord ++ tailWord_6297119) baseStart_6297119 baseEnd_6297119 := by
    simpa [prefixWord, tailWord_6297119, baseEnd_6297119] using wordTrace_append hprefix tailTrace_6297119
  have hstable : (prefixWord ++ tailWord_6297119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297119).length < 2 ^ (prefixWord ++ tailWord_6297119).sum := by decide
  have hdescent : baseEnd_6297119 < baseStart_6297119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297189 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 5]
def baseStart_6297189 : Nat := 118140960795 + 6297189 * 2 ^ 59
def prefixEnd_6297189 : Nat := 4983230072969 + 3 ^ 40 * 6297189 * 2
def baseEnd_6297189 : Nat := 359276081022851994753029

theorem tailTrace_6297189 : CollatzResearch.WordTrace tailWord_6297189 prefixEnd_6297189 359276081022851994753029 := by
  unfold tailWord_6297189
  simp only [CollatzResearch.WordTrace]
  refine ⟨229677351583367202103430621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153118234388911468068953747 229677351583367202103430621)
  ·
    refine ⟨86129006843762700788786483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229677351583367202103430621 86129006843762700788786483)
    ·
      refine ⟨129193510265644051183179725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86129006843762700788786483 129193510265644051183179725)
      ·
        refine ⟨48447566349616519193692397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129193510265644051183179725 48447566349616519193692397)
        ·
          refine ⟨18167837381106194697634649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48447566349616519193692397 18167837381106194697634649)
          ·
            refine ⟨13625878035829646023225987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18167837381106194697634649 13625878035829646023225987)
            ·
              refine ⟨20438817053744469034838981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13625878035829646023225987 20438817053744469034838981)
              ·
                refine ⟨3832278197577087944032309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20438817053744469034838981 3832278197577087944032309)
                ·
                  refine ⟨359276081022851994753029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3832278197577087944032309 359276081022851994753029)
                  ·
                    rfl

theorem cell23_6297189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_6297189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297189 prefixEnd_6297189 := by exact prefixLift 6297189
  have htrace : WordTrace (prefixWord ++ tailWord_6297189) baseStart_6297189 baseEnd_6297189 := by
    simpa [prefixWord, tailWord_6297189, baseEnd_6297189] using wordTrace_append hprefix tailTrace_6297189
  have hstable : (prefixWord ++ tailWord_6297189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297189).length < 2 ^ (prefixWord ++ tailWord_6297189).sum := by decide
  have hdescent : baseEnd_6297189 < baseStart_6297189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297239 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_6297239 : Nat := 118140960795 + 6297239 * 2 ^ 59
def prefixEnd_6297239 : Nat := 4983230072969 + 3 ^ 40 * 6297239 * 2
def baseEnd_6297239 : Nat := 3233510403238392757152031

theorem tailTrace_6297239 : CollatzResearch.WordTrace tailWord_6297239 prefixEnd_6297239 3233510403238392757152031 := by
  unfold tailWord_6297239
  simp only [CollatzResearch.WordTrace]
  refine ⟨229679175233186060642750771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153119450155457373761833847 229679175233186060642750771)
  ·
    refine ⟨344518762849779090964126157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229679175233186060642750771 344518762849779090964126157)
    ·
      refine ⟨129194536068667159111547309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344518762849779090964126157 129194536068667159111547309)
      ·
        refine ⟨48447951025750184666830241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129194536068667159111547309 48447951025750184666830241)
        ·
          refine ⟨36335963269312638500122681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48447951025750184666830241 36335963269312638500122681)
          ·
            refine ⟨27251972451984478875092011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36335963269312638500122681 27251972451984478875092011)
            ·
              refine ⟨40877958677976718312638017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27251972451984478875092011 40877958677976718312638017)
              ·
                refine ⟨30658469008482538734478513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40877958677976718312638017 30658469008482538734478513)
                ·
                  refine ⟨22993851756361904050858885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30658469008482538734478513 22993851756361904050858885)
                  ·
                    refine ⟨4311347204317857009536041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22993851756361904050858885 4311347204317857009536041)
                    ·
                      refine ⟨3233510403238392757152031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311347204317857009536041 3233510403238392757152031)
                      ·
                        rfl

theorem cell23_6297239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_6297239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297239 prefixEnd_6297239 := by exact prefixLift 6297239
  have htrace : WordTrace (prefixWord ++ tailWord_6297239) baseStart_6297239 baseEnd_6297239 := by
    simpa [prefixWord, tailWord_6297239, baseEnd_6297239] using wordTrace_append hprefix tailTrace_6297239
  have hstable : (prefixWord ++ tailWord_6297239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297239).length < 2 ^ (prefixWord ++ tailWord_6297239).sum := by decide
  have hdescent : baseEnd_6297239 < baseStart_6297239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297249 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_6297249 : Nat := 118140960795 + 6297249 * 2 ^ 59
def prefixEnd_6297249 : Nat := 4983230072969 + 3 ^ 40 * 6297249 * 2
def baseEnd_6297249 : Nat := 1077838512681645906008995

theorem tailTrace_6297249 : CollatzResearch.WordTrace tailWord_6297249 prefixEnd_6297249 1077838512681645906008995 := by
  unfold tailWord_6297249
  simp only [CollatzResearch.WordTrace]
  refine ⟨229679539963149832350614801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153119693308766554900409867 229679539963149832350614801)
  ·
    refine ⟨172259654972362374262961101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229679539963149832350614801 172259654972362374262961101)
    ·
      refine ⟨64597370614635890348610413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172259654972362374262961101 64597370614635890348610413)
      ·
        refine ⟨24224013980488458880728905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64597370614635890348610413 24224013980488458880728905)
        ·
          refine ⟨18168010485366344160546679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24224013980488458880728905 18168010485366344160546679)
          ·
            refine ⟨27252015728049516240820019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18168010485366344160546679 27252015728049516240820019)
            ·
              refine ⟨40878023592074274361230029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27252015728049516240820019 40878023592074274361230029)
              ·
                refine ⟨15329258847027852885461261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40878023592074274361230029 15329258847027852885461261)
                ·
                  refine ⟨5748472067635444832047973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15329258847027852885461261 5748472067635444832047973)
                  ·
                    refine ⟨1077838512681645906008995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748472067635444832047973 1077838512681645906008995)
                    ·
                      rfl

theorem cell23_6297249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_6297249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297249 prefixEnd_6297249 := by exact prefixLift 6297249
  have htrace : WordTrace (prefixWord ++ tailWord_6297249) baseStart_6297249 baseEnd_6297249 := by
    simpa [prefixWord, tailWord_6297249, baseEnd_6297249] using wordTrace_append hprefix tailTrace_6297249
  have hstable : (prefixWord ++ tailWord_6297249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297249).length < 2 ^ (prefixWord ++ tailWord_6297249).sum := by decide
  have hdescent : baseEnd_6297249 < baseStart_6297249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297275 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 9]
def baseStart_6297275 : Nat := 118140960795 + 6297275 * 2 ^ 59
def prefixEnd_6297275 : Nat := 4983230072969 + 3 ^ 40 * 6297275 * 2
def baseEnd_6297275 : Nat := 1077842962847318205433955

theorem tailTrace_6297275 : CollatzResearch.WordTrace tailWord_6297275 prefixEnd_6297275 1077842962847318205433955 := by
  unfold tailWord_6297275
  simp only [CollatzResearch.WordTrace]
  refine ⟨229680488261055638791061279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153120325507370425860707519 229680488261055638791061279)
  ·
    refine ⟨344520732391583458186591919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229680488261055638791061279 344520732391583458186591919)
    ·
      refine ⟨516781098587375187279887879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344520732391583458186591919 516781098587375187279887879)
      ·
        refine ⟨775171647881062780919831819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516781098587375187279887879 775171647881062780919831819)
        ·
          refine ⟨1162757471821594171379747729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775171647881062780919831819 1162757471821594171379747729)
          ·
            refine ⟨872068103866195628534810797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162757471821594171379747729 872068103866195628534810797)
            ·
              refine ⟨327025538949823360700554049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872068103866195628534810797 327025538949823360700554049)
              ·
                refine ⟨245269154212367520525415537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327025538949823360700554049 245269154212367520525415537)
                ·
                  refine ⟨183951865659275640394061653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245269154212367520525415537 183951865659275640394061653)
                  ·
                    refine ⟨1077842962847318205433955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183951865659275640394061653 1077842962847318205433955)
                    ·
                      rfl

theorem cell23_6297275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_6297275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297275 prefixEnd_6297275 := by exact prefixLift 6297275
  have htrace : WordTrace (prefixWord ++ tailWord_6297275) baseStart_6297275 baseEnd_6297275 := by
    simpa [prefixWord, tailWord_6297275, baseEnd_6297275] using wordTrace_append hprefix tailTrace_6297275
  have hstable : (prefixWord ++ tailWord_6297275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297275).length < 2 ^ (prefixWord ++ tailWord_6297275).sum := by decide
  have hdescent : baseEnd_6297275 < baseStart_6297275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297293 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6297293 : Nat := 118140960795 + 6297293 * 2 ^ 59
def prefixEnd_6297293 : Nat := 4983230072969 + 3 ^ 40 * 6297293 * 2
def baseEnd_6297293 : Nat := 3233538131193735545876783

theorem tailTrace_6297293 : CollatzResearch.WordTrace tailWord_6297293 prefixEnd_6297293 3233538131193735545876783 := by
  unfold tailWord_6297293
  simp only [CollatzResearch.WordTrace]
  refine ⟨229681144774990427865216533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153120763183326951910144355 229681144774990427865216533)
  ·
    refine ⟨10766303661327676306182025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229681144774990427865216533 10766303661327676306182025)
    ·
      refine ⟨8074727745995757229636519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10766303661327676306182025 8074727745995757229636519)
      ·
        refine ⟨12112091618993635844454779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8074727745995757229636519 12112091618993635844454779)
        ·
          refine ⟨18168137428490453766682169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112091618993635844454779 18168137428490453766682169)
          ·
            refine ⟨13626103071367840325011627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18168137428490453766682169 13626103071367840325011627)
            ·
              refine ⟨20439154607051760487517441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626103071367840325011627 20439154607051760487517441)
              ·
                refine ⟨15329365955288820365638081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20439154607051760487517441 15329365955288820365638081)
                ·
                  refine ⟨11497024466466615274228561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15329365955288820365638081 11497024466466615274228561)
                  ·
                    refine ⟨8622768349849961455671421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11497024466466615274228561 8622768349849961455671421)
                    ·
                      refine ⟨3233538131193735545876783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8622768349849961455671421 3233538131193735545876783)
                      ·
                        rfl

theorem cell23_6297293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6297293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297293 prefixEnd_6297293 := by exact prefixLift 6297293
  have htrace : WordTrace (prefixWord ++ tailWord_6297293) baseStart_6297293 baseEnd_6297293 := by
    simpa [prefixWord, tailWord_6297293, baseEnd_6297293] using wordTrace_append hprefix tailTrace_6297293
  have hstable : (prefixWord ++ tailWord_6297293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297293).length < 2 ^ (prefixWord ++ tailWord_6297293).sum := by decide
  have hdescent : baseEnd_6297293 < baseStart_6297293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297300 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_6297300 : Nat := 118140960795 + 6297300 * 2 ^ 59
def prefixEnd_6297300 : Nat := 4983230072969 + 3 ^ 40 * 6297300 * 2
def baseEnd_6297300 : Nat := 1077847241852772339496417

theorem tailTrace_6297300 : CollatzResearch.WordTrace tailWord_6297300 prefixEnd_6297300 1077847241852772339496417 := by
  unfold tailWord_6297300
  simp only [CollatzResearch.WordTrace]
  refine ⟨114840700042982534030360677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153120933390643378707147569 114840700042982534030360677)
  ·
    refine ⟨21532631258059225130692627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114840700042982534030360677 21532631258059225130692627)
    ·
      refine ⟨32298946887088837696038941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21532631258059225130692627 32298946887088837696038941)
      ·
        refine ⟨12112105082658314136014603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32298946887088837696038941 12112105082658314136014603)
        ·
          refine ⟨18168157623987471204021905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112105082658314136014603 18168157623987471204021905)
          ·
            refine ⟨13626118217990603403016429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18168157623987471204021905 13626118217990603403016429)
            ·
              refine ⟨5109794331746476276131161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13626118217990603403016429 5109794331746476276131161)
              ·
                refine ⟨3832345748809857207098371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5109794331746476276131161 3832345748809857207098371)
                ·
                  refine ⟨5748518623214785810647557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832345748809857207098371 5748518623214785810647557)
                  ·
                    refine ⟨1077847241852772339496417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748518623214785810647557 1077847241852772339496417)
                    ·
                      rfl

theorem cell23_6297300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_6297300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297300 prefixEnd_6297300 := by exact prefixLift 6297300
  have htrace : WordTrace (prefixWord ++ tailWord_6297300) baseStart_6297300 baseEnd_6297300 := by
    simpa [prefixWord, tailWord_6297300, baseEnd_6297300] using wordTrace_append hprefix tailTrace_6297300
  have hstable : (prefixWord ++ tailWord_6297300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297300).length < 2 ^ (prefixWord ++ tailWord_6297300).sum := by decide
  have hdescent : baseEnd_6297300 < baseStart_6297300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297306 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_6297306 : Nat := 118140960795 + 6297306 * 2 ^ 59
def prefixEnd_6297306 : Nat := 4983230072969 + 3 ^ 40 * 6297306 * 2
def baseEnd_6297306 : Nat := 3233544806442243995014223

theorem tailTrace_6297306 : CollatzResearch.WordTrace tailWord_6297306 prefixEnd_6297306 3233544806442243995014223 := by
  unfold tailWord_6297306
  simp only [CollatzResearch.WordTrace]
  refine ⟨57420404730985832771359943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153121079282628887390293181 57420404730985832771359943)
  ·
    refine ⟨86130607096478749157039915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57420404730985832771359943 86130607096478749157039915)
    ·
      refine ⟨129195910644718123735559873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86130607096478749157039915 129195910644718123735559873)
      ·
        refine ⟨96896932983538592801669905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129195910644718123735559873 96896932983538592801669905)
        ·
          refine ⟨72672699737653944601252429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96896932983538592801669905 72672699737653944601252429)
          ·
            refine ⟨27252262401620229225469661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72672699737653944601252429 27252262401620229225469661)
            ·
              refine ⟨10219598400607585959551123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27252262401620229225469661 10219598400607585959551123)
              ·
                refine ⟨15329397600911378939326685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219598400607585959551123 15329397600911378939326685)
                ·
                  refine ⟨5748524100341767102247507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15329397600911378939326685 5748524100341767102247507)
                  ·
                    refine ⟨8622786150512650653371261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5748524100341767102247507 8622786150512650653371261)
                    ·
                      refine ⟨3233544806442243995014223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8622786150512650653371261 3233544806442243995014223)
                      ·
                        rfl

theorem cell23_6297306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_6297306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297306 prefixEnd_6297306 := by exact prefixLift 6297306
  have htrace : WordTrace (prefixWord ++ tailWord_6297306) baseStart_6297306 baseEnd_6297306 := by
    simpa [prefixWord, tailWord_6297306, baseEnd_6297306] using wordTrace_append hprefix tailTrace_6297306
  have hstable : (prefixWord ++ tailWord_6297306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297306).length < 2 ^ (prefixWord ++ tailWord_6297306).sum := by decide
  have hdescent : baseEnd_6297306 < baseStart_6297306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297313 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 6]
def baseStart_6297313 : Nat := 118140960795 + 6297313 * 2 ^ 59
def prefixEnd_6297313 : Nat := 4983230072969 + 3 ^ 40 * 6297313 * 2
def baseEnd_6297313 : Nat := 359283155645202829736299

theorem tailTrace_6297313 : CollatzResearch.WordTrace tailWord_6297313 prefixEnd_6297313 359283155645202829736299 := by
  unfold tailWord_6297313
  simp only [CollatzResearch.WordTrace]
  refine ⟨229681874234917971280944593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153121249489945314187296395 229681874234917971280944593)
  ·
    refine ⟨172261405676188478460708445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229681874234917971280944593 172261405676188478460708445)
    ·
      refine ⟨64598027128570679422765667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172261405676188478460708445 64598027128570679422765667)
      ·
        refine ⟨96897040692856019134148501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64598027128570679422765667 96897040692856019134148501)
        ·
          refine ⟨4542048782477625896913211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96897040692856019134148501 4542048782477625896913211)
          ·
            refine ⟨6813073173716438845369817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542048782477625896913211 6813073173716438845369817)
            ·
              refine ⟨5109804880287329134027363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6813073173716438845369817 5109804880287329134027363)
              ·
                refine ⟨7664707320430993701041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5109804880287329134027363 7664707320430993701041045)
                ·
                  refine ⟨359283155645202829736299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7664707320430993701041045 359283155645202829736299)
                  ·
                    rfl

theorem cell23_6297313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 6].length) (baseStart_6297313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297313 prefixEnd_6297313 := by exact prefixLift 6297313
  have htrace : WordTrace (prefixWord ++ tailWord_6297313) baseStart_6297313 baseEnd_6297313 := by
    simpa [prefixWord, tailWord_6297313, baseEnd_6297313] using wordTrace_append hprefix tailTrace_6297313
  have hstable : (prefixWord ++ tailWord_6297313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297313).length < 2 ^ (prefixWord ++ tailWord_6297313).sum := by decide
  have hdescent : baseEnd_6297313 < baseStart_6297313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297329 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_6297329 : Nat := 118140960795 + 6297329 * 2 ^ 59
def prefixEnd_6297329 : Nat := 4983230072969 + 3 ^ 40 * 6297329 * 2
def baseEnd_6297329 : Nat := 3233556616497297405026617

theorem tailTrace_6297329 : CollatzResearch.WordTrace tailWord_6297329 prefixEnd_6297329 3233556616497297405026617 := by
  unfold tailWord_6297329
  simp only [CollatzResearch.WordTrace]
  refine ⟨229682457802860006013527041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153121638535240004009018027 229682457802860006013527041)
  ·
    refine ⟨172261843352145004510145281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229682457802860006013527041 172261843352145004510145281)
    ·
      refine ⟨129196382514108753382608961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172261843352145004510145281 129196382514108753382608961)
      ·
        refine ⟨96897286885581565036956721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129196382514108753382608961 96897286885581565036956721)
        ·
          refine ⟨72672965164186173777717541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96897286885581565036956721 72672965164186173777717541)
          ·
            refine ⟨13626180968284907583322039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72672965164186173777717541 13626180968284907583322039)
            ·
              refine ⟨20439271452427361374983059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626180968284907583322039 20439271452427361374983059)
              ·
                refine ⟨30658907178641042062474589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20439271452427361374983059 30658907178641042062474589)
                ·
                  refine ⟨11497090191990390773427971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30658907178641042062474589 11497090191990390773427971)
                  ·
                    refine ⟨17245635287985586160141957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11497090191990390773427971 17245635287985586160141957)
                    ·
                      refine ⟨3233556616497297405026617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17245635287985586160141957 3233556616497297405026617)
                      ·
                        rfl

theorem cell23_6297329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_6297329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297329 prefixEnd_6297329 := by exact prefixLift 6297329
  have htrace : WordTrace (prefixWord ++ tailWord_6297329) baseStart_6297329 baseEnd_6297329 := by
    simpa [prefixWord, tailWord_6297329, baseEnd_6297329] using wordTrace_append hprefix tailTrace_6297329
  have hstable : (prefixWord ++ tailWord_6297329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297329).length < 2 ^ (prefixWord ++ tailWord_6297329).sum := by decide
  have hdescent : baseEnd_6297329 < baseStart_6297329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297379 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3]
def baseStart_6297379 : Nat := 118140960795 + 6297379 * 2 ^ 59
def prefixEnd_6297379 : Nat := 4983230072969 + 3 ^ 40 * 6297379 * 2
def baseEnd_6297379 : Nat := 3233582290530022209401387

theorem tailTrace_6297379 : CollatzResearch.WordTrace tailWord_6297379 prefixEnd_6297379 3233582290530022209401387 := by
  unfold tailWord_6297379
  simp only [CollatzResearch.WordTrace]
  refine ⟨229684281452678864552847191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153122854301785909701898127 229684281452678864552847191)
  ·
    refine ⟨344526422179018296829270787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229684281452678864552847191 344526422179018296829270787)
    ·
      refine ⟨516789633268527445243906181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344526422179018296829270787 516789633268527445243906181)
      ·
        refine ⟨96898056237848895983232409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516789633268527445243906181 96898056237848895983232409)
        ·
          refine ⟨72673542178386671987424307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96898056237848895983232409 72673542178386671987424307)
          ·
            refine ⟨109010313267580007981136461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72673542178386671987424307 109010313267580007981136461)
            ·
              refine ⟨40878867475342502992926173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109010313267580007981136461 40878867475342502992926173)
              ·
                refine ⟨15329575303253438622347315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40878867475342502992926173 15329575303253438622347315)
                ·
                  refine ⟨22994362954880157933520973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15329575303253438622347315 22994362954880157933520973)
                  ·
                    refine ⟨8622886108080059225070365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22994362954880157933520973 8622886108080059225070365)
                    ·
                      refine ⟨3233582290530022209401387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8622886108080059225070365 3233582290530022209401387)
                      ·
                        rfl

theorem cell23_6297379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_6297379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297379 prefixEnd_6297379 := by exact prefixLift 6297379
  have htrace : WordTrace (prefixWord ++ tailWord_6297379) baseStart_6297379 baseEnd_6297379 := by
    simpa [prefixWord, tailWord_6297379, baseEnd_6297379] using wordTrace_append hprefix tailTrace_6297379
  have hstable : (prefixWord ++ tailWord_6297379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297379).length < 2 ^ (prefixWord ++ tailWord_6297379).sum := by decide
  have hdescent : baseEnd_6297379 < baseStart_6297379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297397 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_6297397 : Nat := 118140960795 + 6297397 * 2 ^ 59
def prefixEnd_6297397 : Nat := 4983230072969 + 3 ^ 40 * 6297397 * 2
def baseEnd_6297397 : Nat := 3233591533181803138976305

theorem tailTrace_6297397 : CollatzResearch.WordTrace tailWord_6297397 prefixEnd_6297397 3233591533181803138976305 := by
  unfold tailWord_6297397
  simp only [CollatzResearch.WordTrace]
  refine ⟨229684937966613653627002445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153123291977742435751334963 229684937966613653627002445)
  ·
    refine ⟨86131851737480120110125917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229684937966613653627002445 86131851737480120110125917)
    ·
      refine ⟨32299444401555045041297219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86131851737480120110125917 32299444401555045041297219)
      ·
        refine ⟨48449166602332567561945829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32299444401555045041297219 48449166602332567561945829)
        ·
          refine ⟨9084218737937356417864843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48449166602332567561945829 9084218737937356417864843)
          ·
            refine ⟨13626328106906034626797265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084218737937356417864843 13626328106906034626797265)
            ·
              refine ⟨10219746080179525970097949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13626328106906034626797265 10219746080179525970097949)
              ·
                refine ⟨3832404780067322238786731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10219746080179525970097949 3832404780067322238786731)
                ·
                  refine ⟨5748607170100983358180097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832404780067322238786731 5748607170100983358180097)
                  ·
                    refine ⟨4311455377575737518635073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748607170100983358180097 4311455377575737518635073)
                    ·
                      refine ⟨3233591533181803138976305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311455377575737518635073 3233591533181803138976305)
                      ·
                        rfl

theorem cell23_6297397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_6297397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297397 prefixEnd_6297397 := by exact prefixLift 6297397
  have htrace : WordTrace (prefixWord ++ tailWord_6297397) baseStart_6297397 baseEnd_6297397 := by
    simpa [prefixWord, tailWord_6297397, baseEnd_6297397] using wordTrace_append hprefix tailTrace_6297397
  have hstable : (prefixWord ++ tailWord_6297397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297397).length < 2 ^ (prefixWord ++ tailWord_6297397).sum := by decide
  have hdescent : baseEnd_6297397 < baseStart_6297397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297414 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6297414 : Nat := 118140960795 + 6297414 * 2 ^ 59
def prefixEnd_6297414 : Nat := 4983230072969 + 3 ^ 40 * 6297414 * 2
def baseEnd_6297414 : Nat := 3233600262352929572463727

theorem tailTrace_6297414 : CollatzResearch.WordTrace tailWord_6297414 prefixEnd_6297414 3233600262352929572463727 := by
  unfold tailWord_6297414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177673687736002047824103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153123705338368043686914197 7177673687736002047824103)
  ·
    refine ⟨10766510531604003071736155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177673687736002047824103 10766510531604003071736155)
    ·
      refine ⟨16149765797406004607604233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766510531604003071736155 16149765797406004607604233)
      ·
        refine ⟨12112324348054503455703175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16149765797406004607604233 12112324348054503455703175)
        ·
          refine ⟨18168486522081755183554763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112324348054503455703175 18168486522081755183554763)
          ·
            refine ⟨27252729783122632775332145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18168486522081755183554763 27252729783122632775332145)
            ·
              refine ⟨20439547337341974581499109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27252729783122632775332145 20439547337341974581499109)
              ·
                refine ⟨3832415125751620234031083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20439547337341974581499109 3832415125751620234031083)
                ·
                  refine ⟨5748622688627430351046625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832415125751620234031083 5748622688627430351046625)
                  ·
                    refine ⟨4311467016470572763284969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748622688627430351046625 4311467016470572763284969)
                    ·
                      refine ⟨3233600262352929572463727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311467016470572763284969 3233600262352929572463727)
                      ·
                        rfl

theorem cell23_6297414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6297414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297414 prefixEnd_6297414 := by exact prefixLift 6297414
  have htrace : WordTrace (prefixWord ++ tailWord_6297414) baseStart_6297414 baseEnd_6297414 := by
    simpa [prefixWord, tailWord_6297414, baseEnd_6297414] using wordTrace_append hprefix tailTrace_6297414
  have hstable : (prefixWord ++ tailWord_6297414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297414).length < 2 ^ (prefixWord ++ tailWord_6297414).sum := by decide
  have hdescent : baseEnd_6297414 < baseStart_6297414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297419 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 10, 2]
def baseStart_6297419 : Nat := 118140960795 + 6297419 * 2 ^ 59
def prefixEnd_6297419 : Nat := 4983230072969 + 3 ^ 40 * 6297419 * 2
def baseEnd_6297419 : Nat := 3233602829756202052901203

theorem tailTrace_6297419 : CollatzResearch.WordTrace tailWord_6297419 prefixEnd_6297419 3233602829756202052901203 := by
  unfold tailWord_6297419
  simp only [CollatzResearch.WordTrace]
  refine ⟨229685740372533951384303311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153123826915022634256202207 229685740372533951384303311)
  ·
    refine ⟨344528610558800927076454967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229685740372533951384303311 344528610558800927076454967)
    ·
      refine ⟨516792915838201390614682451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344528610558800927076454967 516792915838201390614682451)
      ·
        refine ⟨775189373757302085922023677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516792915838201390614682451 775189373757302085922023677)
        ·
          refine ⟨290696015158988282220758879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 775189373757302085922023677 290696015158988282220758879)
          ·
            refine ⟨436044022738482423331138319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290696015158988282220758879 436044022738482423331138319)
            ·
              refine ⟨654066034107723634996707479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436044022738482423331138319 654066034107723634996707479)
              ·
                refine ⟨981099051161585452495061219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654066034107723634996707479 981099051161585452495061219)
                ·
                  refine ⟨1471648576742378178742591829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981099051161585452495061219 1471648576742378178742591829)
                  ·
                    refine ⟨4311470439674936070534937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1471648576742378178742591829 4311470439674936070534937)
                    ·
                      refine ⟨3233602829756202052901203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311470439674936070534937 3233602829756202052901203)
                      ·
                        rfl

theorem cell23_6297419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10, 2].length) (baseStart_6297419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297419 prefixEnd_6297419 := by exact prefixLift 6297419
  have htrace : WordTrace (prefixWord ++ tailWord_6297419) baseStart_6297419 baseEnd_6297419 := by
    simpa [prefixWord, tailWord_6297419, baseEnd_6297419] using wordTrace_append hprefix tailTrace_6297419
  have hstable : (prefixWord ++ tailWord_6297419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297419).length < 2 ^ (prefixWord ++ tailWord_6297419).sum := by decide
  have hdescent : baseEnd_6297419 < baseStart_6297419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297429 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_6297429 : Nat := 118140960795 + 6297429 * 2 ^ 59
def prefixEnd_6297429 : Nat := 4983230072969 + 3 ^ 40 * 6297429 * 2
def baseEnd_6297429 : Nat := 1077869321520915671258719

theorem tailTrace_6297429 : CollatzResearch.WordTrace tailWord_6297429 prefixEnd_6297429 1077869321520915671258719 := by
  unfold tailWord_6297429
  simp only [CollatzResearch.WordTrace]
  refine ⟨229686105102497723092167341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153124070068331815394778227 229686105102497723092167341)
  ·
    refine ⟨86132289413436646159562753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229686105102497723092167341 86132289413436646159562753)
    ·
      refine ⟨64599217060077484619672065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86132289413436646159562753 64599217060077484619672065)
      ·
        refine ⟨48449412795058113464754049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64599217060077484619672065 48449412795058113464754049)
        ·
          refine ⟨36337059596293585098565537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48449412795058113464754049 36337059596293585098565537)
          ·
            refine ⟨27252794697220188823924153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36337059596293585098565537 27252794697220188823924153)
            ·
              refine ⟨20439596022915141617943115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27252794697220188823924153 20439596022915141617943115)
              ·
                refine ⟨30659394034372712426914673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20439596022915141617943115 30659394034372712426914673)
                ·
                  refine ⟨22994545525779534320186005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30659394034372712426914673 22994545525779534320186005)
                  ·
                    refine ⟨1077869321520915671258719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22994545525779534320186005 1077869321520915671258719)
                    ·
                      rfl

theorem cell23_6297429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_6297429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297429 prefixEnd_6297429 := by exact prefixLift 6297429
  have htrace : WordTrace (prefixWord ++ tailWord_6297429) baseStart_6297429 baseEnd_6297429 := by
    simpa [prefixWord, tailWord_6297429, baseEnd_6297429] using wordTrace_append hprefix tailTrace_6297429
  have hstable : (prefixWord ++ tailWord_6297429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297429).length < 2 ^ (prefixWord ++ tailWord_6297429).sum := by decide
  have hdescent : baseEnd_6297429 < baseStart_6297429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297453 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6297453 : Nat := 118140960795 + 6297453 * 2 ^ 59
def prefixEnd_6297453 : Nat := 4983230072969 + 3 ^ 40 * 6297453 * 2
def baseEnd_6297453 : Nat := 3233620288098454919876047

theorem tailTrace_6297453 : CollatzResearch.WordTrace tailWord_6297453 prefixEnd_6297453 3233620288098454919876047 := by
  unfold tailWord_6297453
  simp only [CollatzResearch.WordTrace]
  refine ⟨229686980454410775191041013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153124653636273850127360675 229686980454410775191041013)
  ·
    refine ⟨21533154417601010174160095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229686980454410775191041013 21533154417601010174160095)
    ·
      refine ⟨32299731626401515261240143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21533154417601010174160095 32299731626401515261240143)
      ·
        refine ⟨48449597439602272891860215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32299731626401515261240143 48449597439602272891860215)
        ·
          refine ⟨72674396159403409337790323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48449597439602272891860215 72674396159403409337790323)
          ·
            refine ⟨109011594239105114006685485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72674396159403409337790323 109011594239105114006685485)
            ·
              refine ⟨40879347839664417752507057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109011594239105114006685485 40879347839664417752507057)
              ·
                refine ⟨30659510879748313314380293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40879347839664417752507057 30659510879748313314380293)
                ·
                  refine ⟨5748658289952808746446305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30659510879748313314380293 5748658289952808746446305)
                  ·
                    refine ⟨4311493717464606559834729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748658289952808746446305 4311493717464606559834729)
                    ·
                      refine ⟨3233620288098454919876047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311493717464606559834729 3233620288098454919876047)
                      ·
                        rfl

theorem cell23_6297453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6297453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297453 prefixEnd_6297453 := by exact prefixLift 6297453
  have htrace : WordTrace (prefixWord ++ tailWord_6297453) baseStart_6297453 baseEnd_6297453 := by
    simpa [prefixWord, tailWord_6297453, baseEnd_6297453] using wordTrace_append hprefix tailTrace_6297453
  have hstable : (prefixWord ++ tailWord_6297453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297453).length < 2 ^ (prefixWord ++ tailWord_6297453).sum := by decide
  have hdescent : baseEnd_6297453 < baseStart_6297453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297476 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 5]
def baseStart_6297476 : Nat := 118140960795 + 6297476 * 2 ^ 59
def prefixEnd_6297476 : Nat := 4983230072969 + 3 ^ 40 * 6297476 * 2
def baseEnd_6297476 : Nat := 359292455350389814432049

theorem tailTrace_6297476 : CollatzResearch.WordTrace tailWord_6297476 prefixEnd_6297476 359292455350389814432049 := by
  unfold tailWord_6297476
  simp only [CollatzResearch.WordTrace]
  refine ⟨114843909666663725059564141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153125212888884966746085521 114843909666663725059564141)
  ·
    refine ⟨43066466124998896897336553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114843909666663725059564141 43066466124998896897336553)
    ·
      refine ⟨32299849593749172673002415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43066466124998896897336553 32299849593749172673002415)
      ·
        refine ⟨48449774390623759009503623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32299849593749172673002415 48449774390623759009503623)
        ·
          refine ⟨72674661585935638514255435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48449774390623759009503623 72674661585935638514255435)
          ·
            refine ⟨109011992378903457771383153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72674661585935638514255435 109011992378903457771383153)
            ·
              refine ⟨81758994284177593328537365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109011992378903457771383153 81758994284177593328537365)
              ·
                refine ⟨3832452857070824687275189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81758994284177593328537365 3832452857070824687275189)
                ·
                  refine ⟨359292455350389814432049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3832452857070824687275189 359292455350389814432049)
                  ·
                    rfl

theorem cell23_6297476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_6297476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297476 prefixEnd_6297476 := by exact prefixLift 6297476
  have htrace : WordTrace (prefixWord ++ tailWord_6297476) baseStart_6297476 baseEnd_6297476 := by
    simpa [prefixWord, tailWord_6297476, baseEnd_6297476] using wordTrace_append hprefix tailTrace_6297476
  have hstable : (prefixWord ++ tailWord_6297476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297476).length < 2 ^ (prefixWord ++ tailWord_6297476).sum := by decide
  have hdescent : baseEnd_6297476 < baseStart_6297476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297509 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_6297509 : Nat := 118140960795 + 6297509 * 2 ^ 59
def prefixEnd_6297509 : Nat := 4983230072969 + 3 ^ 40 * 6297509 * 2
def baseEnd_6297509 : Nat := 3233649043015106700775789

theorem tailTrace_6297509 : CollatzResearch.WordTrace tailWord_6297509 prefixEnd_6297509 3233649043015106700775789 := by
  unfold tailWord_6297509
  simp only [CollatzResearch.WordTrace]
  refine ⟨229689022942207896755079581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153126015294805264503386387 229689022942207896755079581)
  ·
    refine ⟨86133383603327961283154843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229689022942207896755079581 86133383603327961283154843)
    ·
      refine ⟨129200075404991941924732265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86133383603327961283154843 129200075404991941924732265)
      ·
        refine ⟨96900056553743956443549199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129200075404991941924732265 96900056553743956443549199)
        ·
          refine ⟨145350084830615934665323799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96900056553743956443549199 145350084830615934665323799)
          ·
            refine ⟨218025127245923901997985699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145350084830615934665323799 218025127245923901997985699)
            ·
              refine ⟨327037690868885852996978549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218025127245923901997985699 327037690868885852996978549)
              ·
                refine ⟨30659783518958048718466739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327037690868885852996978549 30659783518958048718466739)
                ·
                  refine ⟨45989675278437073077700109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30659783518958048718466739 45989675278437073077700109)
                  ·
                    refine ⟨17246128229413902404137541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45989675278437073077700109 17246128229413902404137541)
                    ·
                      refine ⟨3233649043015106700775789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17246128229413902404137541 3233649043015106700775789)
                      ·
                        rfl

theorem cell23_6297509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_6297509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297509 prefixEnd_6297509 := by exact prefixLift 6297509
  have htrace : WordTrace (prefixWord ++ tailWord_6297509) baseStart_6297509 baseEnd_6297509 := by
    simpa [prefixWord, tailWord_6297509, baseEnd_6297509] using wordTrace_append hprefix tailTrace_6297509
  have hstable : (prefixWord ++ tailWord_6297509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297509).length < 2 ^ (prefixWord ++ tailWord_6297509).sum := by decide
  have hdescent : baseEnd_6297509 < baseStart_6297509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297529 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6297529 : Nat := 118140960795 + 6297529 * 2 ^ 59
def prefixEnd_6297529 : Nat := 4983230072969 + 3 ^ 40 * 6297529 * 2
def baseEnd_6297529 : Nat := 3233659312628196622525697

theorem tailTrace_6297529 : CollatzResearch.WordTrace tailWord_6297529 prefixEnd_6297529 3233659312628196622525697 := by
  unfold tailWord_6297529
  simp only [CollatzResearch.WordTrace]
  refine ⟨229689752402135440170807641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153126501601423626780538427 229689752402135440170807641)
  ·
    refine ⟨172267314301601580128105731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229689752402135440170807641 172267314301601580128105731)
    ·
      refine ⟨258400971452402370192158597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172267314301601580128105731 258400971452402370192158597)
      ·
        refine ⟨48450182147325444411029737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258400971452402370192158597 48450182147325444411029737)
        ·
          refine ⟨36337636610494083308272303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48450182147325444411029737 36337636610494083308272303)
          ·
            refine ⟨54506454915741124962408455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36337636610494083308272303 54506454915741124962408455)
            ·
              refine ⟨81759682373611687443612683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54506454915741124962408455 81759682373611687443612683)
              ·
                refine ⟨122639523560417531165419025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81759682373611687443612683 122639523560417531165419025)
                ·
                  refine ⟨91979642670313148374064269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122639523560417531165419025 91979642670313148374064269)
                  ·
                    refine ⟨34492366001367430640274101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91979642670313148374064269 34492366001367430640274101)
                    ·
                      refine ⟨3233659312628196622525697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34492366001367430640274101 3233659312628196622525697)
                      ·
                        rfl

theorem cell23_6297529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6297529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297529 prefixEnd_6297529 := by exact prefixLift 6297529
  have htrace : WordTrace (prefixWord ++ tailWord_6297529) baseStart_6297529 baseEnd_6297529 := by
    simpa [prefixWord, tailWord_6297529, baseEnd_6297529] using wordTrace_append hprefix tailTrace_6297529
  have hstable : (prefixWord ++ tailWord_6297529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297529).length < 2 ^ (prefixWord ++ tailWord_6297529).sum := by decide
  have hdescent : baseEnd_6297529 < baseStart_6297529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297536 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_6297536 : Nat := 118140960795 + 6297536 * 2 ^ 59
def prefixEnd_6297536 : Nat := 4983230072969 + 3 ^ 40 * 6297536 * 2
def baseEnd_6297536 : Nat := 1077887635664259365046055

theorem tailTrace_6297536 : CollatzResearch.WordTrace tailWord_6297536 prefixEnd_6297536 1077887635664259365046055 := by
  unfold tailWord_6297536
  simp only [CollatzResearch.WordTrace]
  refine ⟨114845003856555040183156231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153126671808740053577541641 114845003856555040183156231)
  ·
    refine ⟨172267505784832560274734347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114845003856555040183156231 172267505784832560274734347)
    ·
      refine ⟨258401258677248840412101521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172267505784832560274734347 258401258677248840412101521)
      ·
        refine ⟨193800944007936630309076141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258401258677248840412101521 193800944007936630309076141)
        ·
          refine ⟨72675354002976236365903553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193800944007936630309076141 72675354002976236365903553)
          ·
            refine ⟨54506515502232177274427665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72675354002976236365903553 54506515502232177274427665)
            ·
              refine ⟨40879886626674132955820749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54506515502232177274427665 40879886626674132955820749)
              ·
                refine ⟨15329957485002799858432781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40879886626674132955820749 15329957485002799858432781)
                ·
                  refine ⟨5748734056876049946912293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15329957485002799858432781 5748734056876049946912293)
                  ·
                    refine ⟨1077887635664259365046055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5748734056876049946912293 1077887635664259365046055)
                    ·
                      rfl

theorem cell23_6297536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_6297536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297536 prefixEnd_6297536 := by exact prefixLift 6297536
  have htrace : WordTrace (prefixWord ++ tailWord_6297536) baseStart_6297536 baseEnd_6297536 := by
    simpa [prefixWord, tailWord_6297536, baseEnd_6297536] using wordTrace_append hprefix tailTrace_6297536
  have hstable : (prefixWord ++ tailWord_6297536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297536).length < 2 ^ (prefixWord ++ tailWord_6297536).sum := by decide
  have hdescent : baseEnd_6297536 < baseStart_6297536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297546 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_6297546 : Nat := 118140960795 + 6297546 * 2 ^ 59
def prefixEnd_6297546 : Nat := 4983230072969 + 3 ^ 40 * 6297546 * 2
def baseEnd_6297546 : Nat := 3233668041799323056013119

theorem tailTrace_6297546 : CollatzResearch.WordTrace tailWord_6297546 prefixEnd_6297546 3233668041799323056013119 := by
  unfold tailWord_6297546
  simp only [CollatzResearch.WordTrace]
  refine ⟨57422593110768463018544123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153126914962049234716117661 57422593110768463018544123)
  ·
    refine ⟨86133889666152694527816185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57422593110768463018544123 86133889666152694527816185)
    ·
      refine ⟨64600417249614520895862139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86133889666152694527816185 64600417249614520895862139)
      ·
        refine ⟨96900625874421781343793209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64600417249614520895862139 96900625874421781343793209)
        ·
          refine ⟨72675469405816336007844907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96900625874421781343793209 72675469405816336007844907)
          ·
            refine ⟨109013204108724504011767361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72675469405816336007844907 109013204108724504011767361)
            ·
              refine ⟨81759903081543378008825521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109013204108724504011767361 81759903081543378008825521)
              ·
                refine ⟨61319927311157533506619141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81759903081543378008825521 61319927311157533506619141)
                ·
                  refine ⟨11497486370842037532491089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61319927311157533506619141 11497486370842037532491089)
                  ·
                    refine ⟨8623114778131528149368317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11497486370842037532491089 8623114778131528149368317)
                    ·
                      refine ⟨3233668041799323056013119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623114778131528149368317 3233668041799323056013119)
                      ·
                        rfl

theorem cell23_6297546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_6297546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297546 prefixEnd_6297546 := by exact prefixLift 6297546
  have htrace : WordTrace (prefixWord ++ tailWord_6297546) baseStart_6297546 baseEnd_6297546 := by
    simpa [prefixWord, tailWord_6297546, baseEnd_6297546] using wordTrace_append hprefix tailTrace_6297546
  have hstable : (prefixWord ++ tailWord_6297546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297546).length < 2 ^ (prefixWord ++ tailWord_6297546).sum := by decide
  have hdescent : baseEnd_6297546 < baseStart_6297546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297593 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 3]
def baseStart_6297593 : Nat := 118140960795 + 6297593 * 2 ^ 59
def prefixEnd_6297593 : Nat := 4983230072969 + 3 ^ 40 * 6297593 * 2
def baseEnd_6297593 : Nat := 3233692175390084372125403

theorem tailTrace_6297593 : CollatzResearch.WordTrace tailWord_6297593 prefixEnd_6297593 3233692175390084372125403 := by
  unfold tailWord_6297593
  simp only [CollatzResearch.WordTrace]
  refine ⟨229692086673903579101137433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153128057782602386067424955 229692086673903579101137433)
  ·
    refine ⟨172269065005427684325853075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229692086673903579101137433 172269065005427684325853075)
    ·
      refine ⟨258403597508141526488779613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172269065005427684325853075 258403597508141526488779613)
      ·
        refine ⟨96901349065553072433292355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258403597508141526488779613 96901349065553072433292355)
        ·
          refine ⟨145352023598329608649938533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96901349065553072433292355 145352023598329608649938533)
          ·
            refine ⟨27253504424686801621863475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145352023598329608649938533 27253504424686801621863475)
            ·
              refine ⟨40880256637030202432795213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27253504424686801621863475 40880256637030202432795213)
              ·
                refine ⟨15330096238886325912298205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40880256637030202432795213 15330096238886325912298205)
                ·
                  refine ⟨5748786089582372217111827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15330096238886325912298205 5748786089582372217111827)
                  ·
                    refine ⟨8623179134373558325667741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5748786089582372217111827 8623179134373558325667741)
                    ·
                      refine ⟨3233692175390084372125403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623179134373558325667741 3233692175390084372125403)
                      ·
                        rfl

theorem cell23_6297593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_6297593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297593 prefixEnd_6297593 := by exact prefixLift 6297593
  have htrace : WordTrace (prefixWord ++ tailWord_6297593) baseStart_6297593 baseEnd_6297593 := by
    simpa [prefixWord, tailWord_6297593, baseEnd_6297593] using wordTrace_append hprefix tailTrace_6297593
  have hstable : (prefixWord ++ tailWord_6297593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297593).length < 2 ^ (prefixWord ++ tailWord_6297593).sum := by decide
  have hdescent : baseEnd_6297593 < baseStart_6297593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297700 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_6297700 : Nat := 118140960795 + 6297700 * 2 ^ 59
def prefixEnd_6297700 : Nat := 4983230072969 + 3 ^ 40 * 6297700 * 2
def baseEnd_6297700 : Nat := 3233747117820115453487411

theorem tailTrace_6297700 : CollatzResearch.WordTrace tailWord_6297700 prefixEnd_6297700 3233747117820115453487411 := by
  unfold tailWord_6297700
  simp only [CollatzResearch.WordTrace]
  refine ⟨114847994642257968187641277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153130659523010624250188369 114847994642257968187641277)
  ·
    refine ⟨43067997990846738070365479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114847994642257968187641277 43067997990846738070365479)
    ·
      refine ⟨64601996986270107105548219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43067997990846738070365479 64601996986270107105548219)
      ·
        refine ⟨96902995479405160658322329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64601996986270107105548219 96902995479405160658322329)
        ·
          refine ⟨72677246609553870493741747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96902995479405160658322329 72677246609553870493741747)
          ·
            refine ⟨109015869914330805740612621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72677246609553870493741747 109015869914330805740612621)
            ·
              refine ⟨40880951217874052152729733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109015869914330805740612621 40880951217874052152729733)
              ·
                refine ⟨7665178353351384778636825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40880951217874052152729733 7665178353351384778636825)
                ·
                  refine ⟨5748883765013538583977619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7665178353351384778636825 5748883765013538583977619)
                  ·
                    refine ⟨8623325647520307875966429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5748883765013538583977619 8623325647520307875966429)
                    ·
                      refine ⟨3233747117820115453487411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623325647520307875966429 3233747117820115453487411)
                      ·
                        rfl

theorem cell23_6297700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_6297700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297700 prefixEnd_6297700 := by exact prefixLift 6297700
  have htrace : WordTrace (prefixWord ++ tailWord_6297700) baseStart_6297700 baseEnd_6297700 := by
    simpa [prefixWord, tailWord_6297700, baseEnd_6297700] using wordTrace_append hprefix tailTrace_6297700
  have hstable : (prefixWord ++ tailWord_6297700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297700).length < 2 ^ (prefixWord ++ tailWord_6297700).sum := by decide
  have hdescent : baseEnd_6297700 < baseStart_6297700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297701 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 1, 2, 2]
def baseStart_6297701 : Nat := 118140960795 + 6297701 * 2 ^ 59
def prefixEnd_6297701 : Nat := 4983230072969 + 3 ^ 40 * 6297701 * 2
def baseEnd_6297701 : Nat := 3233747631300769949574907

theorem tailTrace_6297701 : CollatzResearch.WordTrace tailWord_6297701 prefixEnd_6297701 3233747631300769949574907 := by
  unfold tailWord_6297701
  simp only [CollatzResearch.WordTrace]
  refine ⟨229696025757512313546068957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153130683838341542364045971 229696025757512313546068957)
  ·
    refine ⟨86136009659067117579775859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229696025757512313546068957 86136009659067117579775859)
    ·
      refine ⟨129204014488600676369663789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86136009659067117579775859 129204014488600676369663789)
      ·
        refine ⟨48451505433225253638623921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129204014488600676369663789 48451505433225253638623921)
        ·
          refine ⟨36338629074918940228967941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48451505433225253638623921 36338629074918940228967941)
          ·
            refine ⟨6813492951547301292931489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36338629074918940228967941 6813492951547301292931489)
            ·
              refine ⟨5110119713660475969698617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6813492951547301292931489 5110119713660475969698617)
              ·
                refine ⟨3832589785245356977273963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110119713660475969698617 3832589785245356977273963)
                ·
                  refine ⟨5748884677868035465910945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832589785245356977273963 5748884677868035465910945)
                  ·
                    refine ⟨4311663508401026599433209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748884677868035465910945 4311663508401026599433209)
                    ·
                      refine ⟨3233747631300769949574907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311663508401026599433209 3233747631300769949574907)
                      ·
                        rfl

theorem cell23_6297701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_6297701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297701 prefixEnd_6297701 := by exact prefixLift 6297701
  have htrace : WordTrace (prefixWord ++ tailWord_6297701) baseStart_6297701 baseEnd_6297701 := by
    simpa [prefixWord, tailWord_6297701, baseEnd_6297701] using wordTrace_append hprefix tailTrace_6297701
  have hstable : (prefixWord ++ tailWord_6297701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297701).length < 2 ^ (prefixWord ++ tailWord_6297701).sum := by decide
  have hdescent : baseEnd_6297701 < baseStart_6297701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297710 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_6297710 : Nat := 118140960795 + 6297710 * 2 ^ 59
def prefixEnd_6297710 : Nat := 4983230072969 + 3 ^ 40 * 6297710 * 2
def baseEnd_6297710 : Nat := 3233752252626660414362365

theorem tailTrace_6297710 : CollatzResearch.WordTrace tailWord_6297710 prefixEnd_6297710 3233752252626660414362365 := by
  unfold tailWord_6297710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712044251809963510393323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153130902676319805388764389 28712044251809963510393323)
  ·
    refine ⟨43068066377714945265589985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28712044251809963510393323 43068066377714945265589985)
    ·
      refine ⟨32301049783286208949192489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43068066377714945265589985 32301049783286208949192489)
      ·
        refine ⟨24225787337464656711894367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32301049783286208949192489 24225787337464656711894367)
        ·
          refine ⟨36338681006196985067841551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24225787337464656711894367 36338681006196985067841551)
          ·
            refine ⟨54508021509295477601762327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36338681006196985067841551 54508021509295477601762327)
            ·
              refine ⟨81762032263943216402643491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54508021509295477601762327 81762032263943216402643491)
              ·
                refine ⟨122643048395914824603965237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81762032263943216402643491 122643048395914824603965237)
                ·
                  refine ⟨11497785787117014806621741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122643048395914824603965237 11497785787117014806621741)
                  ·
                    refine ⟨4311669670168880552483153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11497785787117014806621741 4311669670168880552483153)
                    ·
                      refine ⟨3233752252626660414362365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311669670168880552483153 3233752252626660414362365)
                      ·
                        rfl

theorem cell23_6297710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_6297710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297710 prefixEnd_6297710 := by exact prefixLift 6297710
  have htrace : WordTrace (prefixWord ++ tailWord_6297710) baseStart_6297710 baseEnd_6297710 := by
    simpa [prefixWord, tailWord_6297710, baseEnd_6297710] using wordTrace_append hprefix tailTrace_6297710
  have hstable : (prefixWord ++ tailWord_6297710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297710).length < 2 ^ (prefixWord ++ tailWord_6297710).sum := by decide
  have hdescent : baseEnd_6297710 < baseStart_6297710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297757 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_6297757 : Nat := 118140960795 + 6297757 * 2 ^ 59
def prefixEnd_6297757 : Nat := 4983230072969 + 3 ^ 40 * 6297757 * 2
def baseEnd_6297757 : Nat := 3233776386217421730474649

theorem tailTrace_6297757 : CollatzResearch.WordTrace tailWord_6297757 prefixEnd_6297757 3233776386217421730474649 := by
  unfold tailWord_6297757
  simp only [CollatzResearch.WordTrace]
  refine ⟨229698068245309435110107525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153132045496872956740071683 229698068245309435110107525)
  ·
    refine ⟨43068387795995519083145161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229698068245309435110107525 43068387795995519083145161)
    ·
      refine ⟨32301290846996639312358871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43068387795995519083145161 32301290846996639312358871)
      ·
        refine ⟨48451936270494958968538307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32301290846996639312358871 48451936270494958968538307)
        ·
          refine ⟨72677904405742438452807461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48451936270494958968538307 72677904405742438452807461)
          ·
            refine ⟨13627107076076707209901399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72677904405742438452807461 13627107076076707209901399)
            ·
              refine ⟨20440660614115060814852099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13627107076076707209901399 20440660614115060814852099)
              ·
                refine ⟨30660990921172591222278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20440660614115060814852099 30660990921172591222278149)
                ·
                  refine ⟨5748935797719860854177153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30660990921172591222278149 5748935797719860854177153)
                  ·
                    refine ⟨4311701848289895640632865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748935797719860854177153 4311701848289895640632865)
                    ·
                      refine ⟨3233776386217421730474649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311701848289895640632865 3233776386217421730474649)
                      ·
                        rfl

theorem cell23_6297757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_6297757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297757 prefixEnd_6297757 := by exact prefixLift 6297757
  have htrace : WordTrace (prefixWord ++ tailWord_6297757) baseStart_6297757 baseEnd_6297757 := by
    simpa [prefixWord, tailWord_6297757, baseEnd_6297757] using wordTrace_append hprefix tailTrace_6297757
  have hstable : (prefixWord ++ tailWord_6297757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297757).length < 2 ^ (prefixWord ++ tailWord_6297757).sum := by decide
  have hdescent : baseEnd_6297757 < baseStart_6297757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297810 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_6297810 : Nat := 118140960795 + 6297810 * 2 ^ 59
def prefixEnd_6297810 : Nat := 4983230072969 + 3 ^ 40 * 6297810 * 2
def baseEnd_6297810 : Nat := 1077934533564036674370635

theorem tailTrace_6297810 : CollatzResearch.WordTrace tailWord_6297810 prefixEnd_6297810 1077934533564036674370635 := by
  unfold tailWord_6297810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57425000328529356290446721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153133334209411616774524589 57425000328529356290446721)
  ·
    refine ⟨43068750246397017217835041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57425000328529356290446721 43068750246397017217835041)
    ·
      refine ⟨32301562684797762913376281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43068750246397017217835041 32301562684797762913376281)
      ·
        refine ⟨24226172013598322185032211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32301562684797762913376281 24226172013598322185032211)
        ·
          refine ⟨36339258020397483277548317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24226172013598322185032211 36339258020397483277548317)
          ·
            refine ⟨13627221757649056229080619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36339258020397483277548317 13627221757649056229080619)
            ·
              refine ⟨20440832636473584343620929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13627221757649056229080619 20440832636473584343620929)
              ·
                refine ⟨15330624477355188257715697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20440832636473584343620929 15330624477355188257715697)
                ·
                  refine ⟨11497968358016391193286773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15330624477355188257715697 11497968358016391193286773)
                  ·
                    refine ⟨1077934533564036674370635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11497968358016391193286773 1077934533564036674370635)
                    ·
                      rfl

theorem cell23_6297810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_6297810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297810 prefixEnd_6297810 := by exact prefixLift 6297810
  have htrace : WordTrace (prefixWord ++ tailWord_6297810) baseStart_6297810 baseEnd_6297810 := by
    simpa [prefixWord, tailWord_6297810, baseEnd_6297810] using wordTrace_append hprefix tailTrace_6297810
  have hstable : (prefixWord ++ tailWord_6297810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297810).length < 2 ^ (prefixWord ++ tailWord_6297810).sum := by decide
  have hdescent : baseEnd_6297810 < baseStart_6297810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297850 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_6297850 : Nat := 118140960795 + 6297850 * 2 ^ 59
def prefixEnd_6297850 : Nat := 4983230072969 + 3 ^ 40 * 6297850 * 2
def baseEnd_6297850 : Nat := 3233824139918289866611721

theorem tailTrace_6297850 : CollatzResearch.WordTrace tailWord_6297850 prefixEnd_6297850 3233824139918289866611721 := by
  unfold tailWord_6297850
  simp only [CollatzResearch.WordTrace]
  refine ⟨57425365058493127998310751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153134306822648341328828669 57425365058493127998310751)
  ·
    refine ⟨86138047587739691997466127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57425365058493127998310751 86138047587739691997466127)
    ·
      refine ⟨129207071381609537996199191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86138047587739691997466127 129207071381609537996199191)
      ·
        refine ⟨193810607072414306994298787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129207071381609537996199191 193810607072414306994298787)
        ·
          refine ⟨290715910608621460491448181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193810607072414306994298787 290715910608621460491448181)
          ·
            refine ⟨27254616619558261921073267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290715910608621460491448181 27254616619558261921073267)
            ·
              refine ⟨40881924929337392881609901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27254616619558261921073267 40881924929337392881609901)
              ·
                refine ⟨15330721848501522330603713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40881924929337392881609901 15330721848501522330603713)
                ·
                  refine ⟨11498041386376141747952785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15330721848501522330603713 11498041386376141747952785)
                  ·
                    refine ⟨8623531039782106310964589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11498041386376141747952785 8623531039782106310964589)
                    ·
                      refine ⟨3233824139918289866611721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623531039782106310964589 3233824139918289866611721)
                      ·
                        rfl

theorem cell23_6297850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_6297850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297850 prefixEnd_6297850 := by exact prefixLift 6297850
  have htrace : WordTrace (prefixWord ++ tailWord_6297850) baseStart_6297850 baseEnd_6297850 := by
    simpa [prefixWord, tailWord_6297850, baseEnd_6297850] using wordTrace_append hprefix tailTrace_6297850
  have hstable : (prefixWord ++ tailWord_6297850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297850).length < 2 ^ (prefixWord ++ tailWord_6297850).sum := by decide
  have hdescent : baseEnd_6297850 < baseStart_6297850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297857 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6297857 : Nat := 118140960795 + 6297857 * 2 ^ 59
def prefixEnd_6297857 : Nat := 4983230072969 + 3 ^ 40 * 6297857 * 2
def baseEnd_6297857 : Nat := 1077942578094290446408063

theorem tailTrace_6297857 : CollatzResearch.WordTrace tailWord_6297857 prefixEnd_6297857 1077942578094290446408063 := by
  unfold tailWord_6297857
  simp only [CollatzResearch.WordTrace]
  refine ⟨229701715544947152188747825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153134477029964768125831883 229701715544947152188747825)
  ·
    refine ⟨172276286658710364141560869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229701715544947152188747825 172276286658710364141560869)
    ·
      refine ⟨32301803748508193276542663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172276286658710364141560869 32301803748508193276542663)
      ·
        refine ⟨48452705622762289914813995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32301803748508193276542663 48452705622762289914813995)
        ·
          refine ⟨72679058434143434872220993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48452705622762289914813995 72679058434143434872220993)
          ·
            refine ⟨54509293825607576154165745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72679058434143434872220993 54509293825607576154165745)
            ·
              refine ⟨40881970369205682115624309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54509293825607576154165745 40881970369205682115624309)
              ·
                refine ⟨3832684722113032698339779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40881970369205682115624309 3832684722113032698339779)
                ·
                  refine ⟨5749027083169549047509669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832684722113032698339779 5749027083169549047509669)
                  ·
                    refine ⟨1077942578094290446408063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749027083169549047509669 1077942578094290446408063)
                    ·
                      rfl

theorem cell23_6297857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6297857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297857 prefixEnd_6297857 := by exact prefixLift 6297857
  have htrace : WordTrace (prefixWord ++ tailWord_6297857) baseStart_6297857 baseEnd_6297857 := by
    simpa [prefixWord, tailWord_6297857, baseEnd_6297857] using wordTrace_append hprefix tailTrace_6297857
  have hstable : (prefixWord ++ tailWord_6297857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297857).length < 2 ^ (prefixWord ++ tailWord_6297857).sum := by decide
  have hdescent : baseEnd_6297857 < baseStart_6297857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297870 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_6297870 : Nat := 118140960795 + 6297870 * 2 ^ 59
def prefixEnd_6297870 : Nat := 4983230072969 + 3 ^ 40 * 6297870 * 2
def baseEnd_6297870 : Nat := 359314934392375532040181

theorem tailTrace_6297870 : CollatzResearch.WordTrace tailWord_6297870 prefixEnd_6297870 359314934392375532040181 := by
  unfold tailWord_6297870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28712773711737506926121383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153134793129266703605980709 28712773711737506926121383)
  ·
    refine ⟨43069160567606260389182075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28712773711737506926121383 43069160567606260389182075)
    ·
      refine ⟨64603740851409390583773113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43069160567606260389182075 64603740851409390583773113)
      ·
        refine ⟨48452805638557042937829835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64603740851409390583773113 48452805638557042937829835)
        ·
          refine ⟨72679208457835564406744753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48452805638557042937829835 72679208457835564406744753)
          ·
            refine ⟨54509406343376673305058565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72679208457835564406744753 54509406343376673305058565)
            ·
              refine ⟨10220513689383126244698481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54509406343376673305058565 10220513689383126244698481)
              ·
                refine ⟨7665385267037344683523861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10220513689383126244698481 7665385267037344683523861)
                ·
                  refine ⟨359314934392375532040181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7665385267037344683523861 359314934392375532040181)
                  ·
                    rfl

theorem cell23_6297870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_6297870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297870 prefixEnd_6297870 := by exact prefixLift 6297870
  have htrace : WordTrace (prefixWord ++ tailWord_6297870) baseStart_6297870 baseEnd_6297870 := by
    simpa [prefixWord, tailWord_6297870, baseEnd_6297870] using wordTrace_append hprefix tailTrace_6297870
  have hstable : (prefixWord ++ tailWord_6297870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297870).length < 2 ^ (prefixWord ++ tailWord_6297870).sum := by decide
  have hdescent : baseEnd_6297870 < baseStart_6297870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297883 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 3, 5]
def baseStart_6297883 : Nat := 118140960795 + 6297883 * 2 ^ 59
def prefixEnd_6297883 : Nat := 4983230072969 + 3 ^ 40 * 6297883 * 2
def baseEnd_6297883 : Nat := 1077947028259962745833023

theorem tailTrace_6297883 : CollatzResearch.WordTrace tailWord_6297883 prefixEnd_6297883 1077947028259962745833023 := by
  unfold tailWord_6297883
  simp only [CollatzResearch.WordTrace]
  refine ⟨229702663842852958629194303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153135109228568639086129535 229702663842852958629194303)
  ·
    refine ⟨344553995764279437943791455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229702663842852958629194303 344553995764279437943791455)
    ·
      refine ⟨516830993646419156915687183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344553995764279437943791455 516830993646419156915687183)
      ·
        refine ⟨775246490469628735373530775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516830993646419156915687183 775246490469628735373530775)
        ·
          refine ⟨1162869735704443103060296163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775246490469628735373530775 1162869735704443103060296163)
          ·
            refine ⟨1744304603556664654590444245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162869735704443103060296163 1744304603556664654590444245)
            ·
              refine ⟨40882139145859327841963537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1744304603556664654590444245 40882139145859327841963537)
              ·
                refine ⟨30661604359394495881472653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40882139145859327841963537 30661604359394495881472653)
                ·
                  refine ⟨11498101634772935955552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30661604359394495881472653 11498101634772935955552245)
                  ·
                    refine ⟨1077947028259962745833023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11498101634772935955552245 1077947028259962745833023)
                    ·
                      rfl

theorem cell23_6297883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 5].length) (baseStart_6297883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297883 prefixEnd_6297883 := by exact prefixLift 6297883
  have htrace : WordTrace (prefixWord ++ tailWord_6297883) baseStart_6297883 baseEnd_6297883 := by
    simpa [prefixWord, tailWord_6297883, baseEnd_6297883] using wordTrace_append hprefix tailTrace_6297883
  have hstable : (prefixWord ++ tailWord_6297883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297883).length < 2 ^ (prefixWord ++ tailWord_6297883).sum := by decide
  have hdescent : baseEnd_6297883 < baseStart_6297883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297901 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6297901 : Nat := 118140960795 + 6297901 * 2 ^ 59
def prefixEnd_6297901 : Nat := 4983230072969 + 3 ^ 40 * 6297901 * 2
def baseEnd_6297901 : Nat := 3233850327431669167073987

theorem tailTrace_6297901 : CollatzResearch.WordTrace tailWord_6297901 prefixEnd_6297901 3233850327431669167073987 := by
  unfold tailWord_6297901
  simp only [CollatzResearch.WordTrace]
  refine ⟨229703320356787747703349557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153135546904525165135566371 229703320356787747703349557)
  ·
    refine ⟨21534686283448851347189021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229703320356787747703349557 21534686283448851347189021)
    ·
      refine ⟨8075507356293319255195883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21534686283448851347189021 8075507356293319255195883)
      ·
        refine ⟨12113261034439978882793825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075507356293319255195883 12113261034439978882793825)
        ·
          refine ⟨9084945775829984162095369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12113261034439978882793825 9084945775829984162095369)
          ·
            refine ⟨6813709331872488121571527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9084945775829984162095369 6813709331872488121571527)
            ·
              refine ⟨10220563997808732182357291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813709331872488121571527 10220563997808732182357291)
              ·
                refine ⟨15330845996713098273535937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10220563997808732182357291 15330845996713098273535937)
                ·
                  refine ⟨11498134497534823705151953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15330845996713098273535937 11498134497534823705151953)
                  ·
                    refine ⟨8623600873151117778863965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11498134497534823705151953 8623600873151117778863965)
                    ·
                      refine ⟨3233850327431669167073987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623600873151117778863965 3233850327431669167073987)
                      ·
                        rfl

theorem cell23_6297901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6297901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297901 prefixEnd_6297901 := by exact prefixLift 6297901
  have htrace : WordTrace (prefixWord ++ tailWord_6297901) baseStart_6297901 baseEnd_6297901 := by
    simpa [prefixWord, tailWord_6297901, baseEnd_6297901] using wordTrace_append hprefix tailTrace_6297901
  have hstable : (prefixWord ++ tailWord_6297901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297901).length < 2 ^ (prefixWord ++ tailWord_6297901).sum := by decide
  have hdescent : baseEnd_6297901 < baseStart_6297901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297914 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3]
def baseStart_6297914 : Nat := 118140960795 + 6297914 * 2 ^ 59
def prefixEnd_6297914 : Nat := 4983230072969 + 3 ^ 40 * 6297914 * 2
def baseEnd_6297914 : Nat := 3233857002680177616211427

theorem tailTrace_6297914 : CollatzResearch.WordTrace tailWord_6297914 prefixEnd_6297914 3233857002680177616211427 := by
  unfold tailWord_6297914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57425948626435162730893199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153135863003827100615715197 57425948626435162730893199)
  ·
    refine ⟨86138922939652744096339799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57425948626435162730893199 86138922939652744096339799)
    ·
      refine ⟨129208384409479116144509699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86138922939652744096339799 129208384409479116144509699)
      ·
        refine ⟨193812576614218674216764549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129208384409479116144509699 193812576614218674216764549)
        ·
          refine ⟨36339858115166001415643353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193812576614218674216764549 36339858115166001415643353)
          ·
            refine ⟨27254893586374501061732515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36339858115166001415643353 27254893586374501061732515)
            ·
              refine ⟨40882340379561751592598773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27254893586374501061732515 40882340379561751592598773)
              ·
                refine ⟨3832719410583914211806135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40882340379561751592598773 3832719410583914211806135)
                ·
                  refine ⟨5749079115875871317709203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832719410583914211806135 5749079115875871317709203)
                  ·
                    refine ⟨8623618673813806976563805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5749079115875871317709203 8623618673813806976563805)
                    ·
                      refine ⟨3233857002680177616211427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623618673813806976563805 3233857002680177616211427)
                      ·
                        rfl

theorem cell23_6297914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_6297914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297914 prefixEnd_6297914 := by exact prefixLift 6297914
  have htrace : WordTrace (prefixWord ++ tailWord_6297914) baseStart_6297914 baseEnd_6297914 := by
    simpa [prefixWord, tailWord_6297914, baseEnd_6297914] using wordTrace_append hprefix tailTrace_6297914
  have hstable : (prefixWord ++ tailWord_6297914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297914).length < 2 ^ (prefixWord ++ tailWord_6297914).sum := by decide
  have hdescent : baseEnd_6297914 < baseStart_6297914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297940 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6297940 : Nat := 118140960795 + 6297940 * 2 ^ 59
def prefixEnd_6297940 : Nat := 4983230072969 + 3 ^ 40 * 6297940 * 2
def baseEnd_6297940 : Nat := 3233870353177194514486307

theorem tailTrace_6297940 : CollatzResearch.WordTrace tailWord_6297940 prefixEnd_6297940 3233870353177194514486307 := by
  unfold tailWord_6297940
  simp only [CollatzResearch.WordTrace]
  refine ⟨114852371401823228682009637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153136495202430971576012849 114852371401823228682009637)
  ·
    refine ⟨21534819637841855377876807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114852371401823228682009637 21534819637841855377876807)
    ·
      refine ⟨32302229456762783066815211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21534819637841855377876807 32302229456762783066815211)
      ·
        refine ⟨48453344185144174600222817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32302229456762783066815211 48453344185144174600222817)
        ·
          refine ⟨36340008138858130950167113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48453344185144174600222817 36340008138858130950167113)
          ·
            refine ⟨27255006104143598212625335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36340008138858130950167113 27255006104143598212625335)
            ·
              refine ⟨40882509156215397318938003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27255006104143598212625335 40882509156215397318938003)
              ·
                refine ⟨61323763734323095978407005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40882509156215397318938003 61323763734323095978407005)
                ·
                  refine ⟨22996411400371160991902627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61323763734323095978407005 22996411400371160991902627)
                  ·
                    refine ⟨34494617100556741487853941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22996411400371160991902627 34494617100556741487853941)
                    ·
                      refine ⟨3233870353177194514486307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34494617100556741487853941 3233870353177194514486307)
                      ·
                        rfl

theorem cell23_6297940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6297940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297940 prefixEnd_6297940 := by exact prefixLift 6297940
  have htrace : WordTrace (prefixWord ++ tailWord_6297940) baseStart_6297940 baseEnd_6297940 := by
    simpa [prefixWord, tailWord_6297940, baseEnd_6297940] using wordTrace_append hprefix tailTrace_6297940
  have hstable : (prefixWord ++ tailWord_6297940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297940).length < 2 ^ (prefixWord ++ tailWord_6297940).sum := by decide
  have hdescent : baseEnd_6297940 < baseStart_6297940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297943 : List Nat := [1, 1, 3, 2, 3, 1, 2, 10]
def baseStart_6297943 : Nat := 118140960795 + 6297943 * 2 ^ 59
def prefixEnd_6297943 : Nat := 4983230072969 + 3 ^ 40 * 6297943 * 2
def baseEnd_6297943 : Nat := 119773033097005851953659

theorem tailTrace_6297943 : CollatzResearch.WordTrace tailWord_6297943 prefixEnd_6297943 119773033097005851953659 := by
  unfold tailWord_6297943
  simp only [CollatzResearch.WordTrace]
  refine ⟨229704852222635588876378483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153136568148423725917585655 229704852222635588876378483)
  ·
    refine ⟨344557278333953383314567725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229704852222635588876378483 344557278333953383314567725)
    ·
      refine ⟨129208979375232518742962897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344557278333953383314567725 129208979375232518742962897)
      ·
        refine ⟨96906734531424389057222173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129208979375232518742962897 96906734531424389057222173)
        ·
          refine ⟨36340025449284145896458315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96906734531424389057222173 36340025449284145896458315)
          ·
            refine ⟨54510038173926218844687473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36340025449284145896458315 54510038173926218844687473)
            ·
              refine ⟨40882528630444664133515605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54510038173926218844687473 40882528630444664133515605)
              ·
                refine ⟨119773033097005851953659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40882528630444664133515605 119773033097005851953659)
                ·
                  rfl

theorem cell23_6297943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 10].length) (baseStart_6297943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297943 prefixEnd_6297943 := by exact prefixLift 6297943
  have htrace : WordTrace (prefixWord ++ tailWord_6297943) baseStart_6297943 baseEnd_6297943 := by
    simpa [prefixWord, tailWord_6297943, baseEnd_6297943] using wordTrace_append hprefix tailTrace_6297943
  have hstable : (prefixWord ++ tailWord_6297943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297943).length < 2 ^ (prefixWord ++ tailWord_6297943).sum := by decide
  have hdescent : baseEnd_6297943 < baseStart_6297943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297954 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6297954 : Nat := 118140960795 + 6297954 * 2 ^ 59
def prefixEnd_6297954 : Nat := 4983230072969 + 3 ^ 40 * 6297954 * 2
def baseEnd_6297954 : Nat := 3233877541906357459711243

theorem tailTrace_6297954 : CollatzResearch.WordTrace tailWord_6297954 prefixEnd_6297954 3233877541906357459711243 := by
  unfold tailWord_6297954
  simp only [CollatzResearch.WordTrace]
  refine ⟨57426313356398934438757229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153136835617063825170019277 57426313356398934438757229)
  ·
    refine ⟨21534867508649600414533961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57426313356398934438757229 21534867508649600414533961)
    ·
      refine ⟨16151150631487200310900471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21534867508649600414533961 16151150631487200310900471)
      ·
        refine ⟨24226725947230800466350707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151150631487200310900471 24226725947230800466350707)
        ·
          refine ⟨36340088920846200699526061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24226725947230800466350707 36340088920846200699526061)
          ·
            refine ⟨13627533345317325262322273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36340088920846200699526061 13627533345317325262322273)
            ·
              refine ⟨10220650008987993946741705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13627533345317325262322273 10220650008987993946741705)
              ·
                refine ⟨7665487506740995460056279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10220650008987993946741705 7665487506740995460056279)
                ·
                  refine ⟨11498231260111493190084419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7665487506740995460056279 11498231260111493190084419)
                  ·
                    refine ⟨17247346890167239785126629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11498231260111493190084419 17247346890167239785126629)
                    ·
                      refine ⟨3233877541906357459711243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17247346890167239785126629 3233877541906357459711243)
                      ·
                        rfl

theorem cell23_6297954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6297954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297954 prefixEnd_6297954 := by exact prefixLift 6297954
  have htrace : WordTrace (prefixWord ++ tailWord_6297954) baseStart_6297954 baseEnd_6297954 := by
    simpa [prefixWord, tailWord_6297954, baseEnd_6297954] using wordTrace_append hprefix tailTrace_6297954
  have hstable : (prefixWord ++ tailWord_6297954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297954).length < 2 ^ (prefixWord ++ tailWord_6297954).sum := by decide
  have hdescent : baseEnd_6297954 < baseStart_6297954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297957 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_6297957 : Nat := 118140960795 + 6297957 * 2 ^ 59
def prefixEnd_6297957 : Nat := 4983230072969 + 3 ^ 40 * 6297957 * 2
def baseEnd_6297957 : Nat := 3233879082348320947973729

theorem tailTrace_6297957 : CollatzResearch.WordTrace tailWord_6297957 prefixEnd_6297957 3233879082348320947973729 := by
  unfold tailWord_6297957
  simp only [CollatzResearch.WordTrace]
  refine ⟨229705362844584869267388125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153136908563056579511592083 229705362844584869267388125)
  ·
    refine ⟨86139511066719325975270547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229705362844584869267388125 86139511066719325975270547)
    ·
      refine ⟨129209266600078988962905821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86139511066719325975270547 129209266600078988962905821)
      ·
        refine ⟨48453474975029620861089683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129209266600078988962905821 48453474975029620861089683)
        ·
          refine ⟨72680212462544431291634525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48453474975029620861089683 72680212462544431291634525)
          ·
            refine ⟨27255079673454161734362947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72680212462544431291634525 27255079673454161734362947)
            ·
              refine ⟨40882619510181242601544421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27255079673454161734362947 40882619510181242601544421)
              ·
                refine ⟨7665491158158982987789579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40882619510181242601544421 7665491158158982987789579)
                ·
                  refine ⟨11498236737238474481684369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7665491158158982987789579 11498236737238474481684369)
                  ·
                    refine ⟨8623677552928855861263277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11498236737238474481684369 8623677552928855861263277)
                    ·
                      refine ⟨3233879082348320947973729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623677552928855861263277 3233879082348320947973729)
                      ·
                        rfl

theorem cell23_6297957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_6297957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297957 prefixEnd_6297957 := by exact prefixLift 6297957
  have htrace : WordTrace (prefixWord ++ tailWord_6297957) baseStart_6297957 baseEnd_6297957 := by
    simpa [prefixWord, tailWord_6297957, baseEnd_6297957] using wordTrace_append hprefix tailTrace_6297957
  have hstable : (prefixWord ++ tailWord_6297957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297957).length < 2 ^ (prefixWord ++ tailWord_6297957).sum := by decide
  have hdescent : baseEnd_6297957 < baseStart_6297957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297960 : List Nat := [2, 1, 4, 2, 2, 2, 1, 9]
def baseStart_6297960 : Nat := 118140960795 + 6297960 * 2 ^ 59
def prefixEnd_6297960 : Nat := 4983230072969 + 3 ^ 40 * 6297960 * 2
def baseEnd_6297960 : Nat := 119773356399640164305045

theorem tailTrace_6297960 : CollatzResearch.WordTrace tailWord_6297960 prefixEnd_6297960 119773356399640164305045 := by
  unfold tailWord_6297960
  simp only [CollatzResearch.WordTrace]
  refine ⟨114852736131787000389873667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153136981509049333853164889 114852736131787000389873667)
  ·
    refine ⟨172279104197680500584810501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114852736131787000389873667 172279104197680500584810501)
    ·
      refine ⟨32302332037065093859651969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172279104197680500584810501 32302332037065093859651969)
      ·
        refine ⟨24226749027798820394738977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32302332037065093859651969 24226749027798820394738977)
        ·
          refine ⟨18170061770849115296054233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24226749027798820394738977 18170061770849115296054233)
          ·
            refine ⟨13627546328136836472040675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18170061770849115296054233 13627546328136836472040675)
            ·
              refine ⟨20441319492205254708061013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13627546328136836472040675 20441319492205254708061013)
              ·
                refine ⟨119773356399640164305045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20441319492205254708061013 119773356399640164305045)
                ·
                  rfl

theorem cell23_6297960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 9].length) (baseStart_6297960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297960 prefixEnd_6297960 := by exact prefixLift 6297960
  have htrace : WordTrace (prefixWord ++ tailWord_6297960) baseStart_6297960 baseEnd_6297960 := by
    simpa [prefixWord, tailWord_6297960, baseEnd_6297960] using wordTrace_append hprefix tailTrace_6297960
  have hstable : (prefixWord ++ tailWord_6297960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297960).length < 2 ^ (prefixWord ++ tailWord_6297960).sum := by decide
  have hdescent : baseEnd_6297960 < baseStart_6297960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6297988 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_6297988 : Nat := 118140960795 + 6297988 * 2 ^ 59
def prefixEnd_6297988 : Nat := 4983230072969 + 3 ^ 40 * 6297988 * 2
def baseEnd_6297988 : Nat := 3233895000248610326686087

theorem tailTrace_6297988 : CollatzResearch.WordTrace tailWord_6297988 prefixEnd_6297988 3233895000248610326686087 := by
  unfold tailWord_6297988
  simp only [CollatzResearch.WordTrace]
  refine ⟨114853246753736280780883309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153137662338315041041177745 114853246753736280780883309)
  ·
    refine ⟨43069967532651105292831241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114853246753736280780883309 43069967532651105292831241)
    ·
      refine ⟨32302475649488328969623431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43069967532651105292831241 32302475649488328969623431)
      ·
        refine ⟨48453713474232493454435147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32302475649488328969623431 48453713474232493454435147)
        ·
          refine ⟨72680570211348740181652721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48453713474232493454435147 72680570211348740181652721)
          ·
            refine ⟨54510427658511555136239541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72680570211348740181652721 54510427658511555136239541)
            ·
              refine ⟨5110352592985458294022457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54510427658511555136239541 5110352592985458294022457)
              ·
                refine ⟨3832764444739093720516843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110352592985458294022457 3832764444739093720516843)
                ·
                  refine ⟨5749146667108640580775265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832764444739093720516843 5749146667108640580775265)
                  ·
                    refine ⟨4311860000331480435581449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749146667108640580775265 4311860000331480435581449)
                    ·
                      refine ⟨3233895000248610326686087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311860000331480435581449 3233895000248610326686087)
                      ·
                        rfl

theorem cell23_6297988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_6297988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6297988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6297988 prefixEnd_6297988 := by exact prefixLift 6297988
  have htrace : WordTrace (prefixWord ++ tailWord_6297988) baseStart_6297988 baseEnd_6297988 := by
    simpa [prefixWord, tailWord_6297988, baseEnd_6297988] using wordTrace_append hprefix tailTrace_6297988
  have hstable : (prefixWord ++ tailWord_6297988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6297988).length < 2 ^ (prefixWord ++ tailWord_6297988).sum := by decide
  have hdescent : baseEnd_6297988 < baseStart_6297988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6297988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298040 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_6298040 : Nat := 118140960795 + 6298040 * 2 ^ 59
def prefixEnd_6298040 : Nat := 4983230072969 + 3 ^ 40 * 6298040 * 2
def baseEnd_6298040 : Nat := 3233921701242644123235847

theorem tailTrace_6298040 : CollatzResearch.WordTrace tailWord_6298040 prefixEnd_6298040 3233921701242644123235847 := by
  unfold tailWord_6298040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114854195051642087221329787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153138926735522782961773049 114854195051642087221329787)
  ·
    refine ⟨172281292577463130831994681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114854195051642087221329787 172281292577463130831994681)
    ·
      refine ⟨129210969433097348123996011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172281292577463130831994681 129210969433097348123996011)
      ·
        refine ⟨193816454149646022185994017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129210969433097348123996011 193816454149646022185994017)
        ·
          refine ⟨145362340612234516639495513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193816454149646022185994017 145362340612234516639495513)
          ·
            refine ⟨109021755459175887479621635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145362340612234516639495513 109021755459175887479621635)
            ·
              refine ⟨163532633188763831219432453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109021755459175887479621635 163532633188763831219432453)
              ·
                refine ⟨30662368722893218353643585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163532633188763831219432453 30662368722893218353643585)
                ·
                  refine ⟨22996776542169913765232689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30662368722893218353643585 22996776542169913765232689)
                  ·
                    refine ⟨17247582406627435323924517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22996776542169913765232689 17247582406627435323924517)
                    ·
                      refine ⟨3233921701242644123235847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17247582406627435323924517 3233921701242644123235847)
                      ·
                        rfl

theorem cell23_6298040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_6298040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298040 prefixEnd_6298040 := by exact prefixLift 6298040
  have htrace : WordTrace (prefixWord ++ tailWord_6298040) baseStart_6298040 baseEnd_6298040 := by
    simpa [prefixWord, tailWord_6298040, baseEnd_6298040] using wordTrace_append hprefix tailTrace_6298040
  have hstable : (prefixWord ++ tailWord_6298040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298040).length < 2 ^ (prefixWord ++ tailWord_6298040).sum := by decide
  have hdescent : baseEnd_6298040 < baseStart_6298040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298077 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_6298077 : Nat := 118140960795 + 6298077 * 2 ^ 59
def prefixEnd_6298077 : Nat := 4983230072969 + 3 ^ 40 * 6298077 * 2
def baseEnd_6298077 : Nat := 3233940700026860478473177

theorem tailTrace_6298077 : CollatzResearch.WordTrace tailWord_6298077 prefixEnd_6298077 3233940700026860478473177 := by
  unfold tailWord_6298077
  simp only [CollatzResearch.WordTrace]
  refine ⟨229709739604150129761756485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153139826402766753174504323 229709739604150129761756485)
  ·
    refine ⟨43070576175778149330329341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229709739604150129761756485 43070576175778149330329341)
    ·
      refine ⟨16151466065916805998873503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43070576175778149330329341 16151466065916805998873503)
      ·
        refine ⟨24227199098875208998310255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151466065916805998873503 24227199098875208998310255)
        ·
          refine ⟨36340798648312813497465383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227199098875208998310255 36340798648312813497465383)
          ·
            refine ⟨54511197972469220246198075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36340798648312813497465383 54511197972469220246198075)
            ·
              refine ⟨81766796958703830369297113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54511197972469220246198075 81766796958703830369297113)
              ·
                refine ⟨61325097719027872776972835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81766796958703830369297113 61325097719027872776972835)
                ·
                  refine ⟨91987646578541809165459253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61325097719027872776972835 91987646578541809165459253)
                  ·
                    refine ⟨8623841866738294609261805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91987646578541809165459253 8623841866738294609261805)
                    ·
                      refine ⟨3233940700026860478473177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623841866738294609261805 3233940700026860478473177)
                      ·
                        rfl

theorem cell23_6298077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_6298077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298077 prefixEnd_6298077 := by exact prefixLift 6298077
  have htrace : WordTrace (prefixWord ++ tailWord_6298077) baseStart_6298077 baseEnd_6298077 := by
    simpa [prefixWord, tailWord_6298077, baseEnd_6298077] using wordTrace_append hprefix tailTrace_6298077
  have hstable : (prefixWord ++ tailWord_6298077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298077).length < 2 ^ (prefixWord ++ tailWord_6298077).sum := by decide
  have hdescent : baseEnd_6298077 < baseStart_6298077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298080 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_6298080 : Nat := 118140960795 + 6298080 * 2 ^ 59
def prefixEnd_6298080 : Nat := 4983230072969 + 3 ^ 40 * 6298080 * 2
def baseEnd_6298080 : Nat := 1077980746822941322245221

theorem tailTrace_6298080 : CollatzResearch.WordTrace tailWord_6298080 prefixEnd_6298080 1077980746822941322245221 := by
  unfold tailWord_6298080
  simp only [CollatzResearch.WordTrace]
  refine ⟨114854924511569630637057847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153139899348759507516077129 114854924511569630637057847)
  ·
    refine ⟨172282386767354445955586771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114854924511569630637057847 172282386767354445955586771)
    ·
      refine ⟨258423580151031668933380157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172282386767354445955586771 258423580151031668933380157)
      ·
        refine ⟨96908842556636875850017559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258423580151031668933380157 96908842556636875850017559)
        ·
          refine ⟨145363263834955313775026339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96908842556636875850017559 145363263834955313775026339)
          ·
            refine ⟨218044895752432970662539509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145363263834955313775026339 218044895752432970662539509)
            ·
              refine ⟨20441708976790590999613079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218044895752432970662539509 20441708976790590999613079)
              ·
                refine ⟨30662563465185886499419619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20441708976790590999613079 30662563465185886499419619)
                ·
                  refine ⟨45993845197778829749129429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30662563465185886499419619 45993845197778829749129429)
                  ·
                    refine ⟨1077980746822941322245221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45993845197778829749129429 1077980746822941322245221)
                    ·
                      rfl

theorem cell23_6298080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_6298080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298080 prefixEnd_6298080 := by exact prefixLift 6298080
  have htrace : WordTrace (prefixWord ++ tailWord_6298080) baseStart_6298080 baseEnd_6298080 := by
    simpa [prefixWord, tailWord_6298080, baseEnd_6298080] using wordTrace_append hprefix tailTrace_6298080
  have hstable : (prefixWord ++ tailWord_6298080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298080).length < 2 ^ (prefixWord ++ tailWord_6298080).sum := by decide
  have hdescent : baseEnd_6298080 < baseStart_6298080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298082 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6298082 : Nat := 118140960795 + 6298082 * 2 ^ 59
def prefixEnd_6298082 : Nat := 4983230072969 + 3 ^ 40 * 6298082 * 2
def baseEnd_6298082 : Nat := 3233943267430132958910655

theorem tailTrace_6298082 : CollatzResearch.WordTrace tailWord_6298082 prefixEnd_6298082 3233943267430132958910655 := by
  unfold tailWord_6298082
  simp only [CollatzResearch.WordTrace]
  refine ⟨57427480492283003903922125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153139947979421343743792333 57427480492283003903922125)
  ·
    refine ⟨21535305184606126463970797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57427480492283003903922125 21535305184606126463970797)
    ·
      refine ⟨8075739444227297423989049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21535305184606126463970797 8075739444227297423989049)
      ·
        refine ⟨6056804583170473067991787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8075739444227297423989049 6056804583170473067991787)
        ·
          refine ⟨9085206874755709601987681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056804583170473067991787 9085206874755709601987681)
          ·
            refine ⟨6813905156066782201490761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9085206874755709601987681 6813905156066782201490761)
            ·
              refine ⟨5110428867050086651118071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6813905156066782201490761 5110428867050086651118071)
              ·
                refine ⟨7665643300575129976677107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110428867050086651118071 7665643300575129976677107)
                ·
                  refine ⟨11498464950862694965015661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7665643300575129976677107 11498464950862694965015661)
                  ·
                    refine ⟨4311924356573510611880873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11498464950862694965015661 4311924356573510611880873)
                    ·
                      refine ⟨3233943267430132958910655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4311924356573510611880873 3233943267430132958910655)
                      ·
                        rfl

theorem cell23_6298082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6298082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298082 prefixEnd_6298082 := by exact prefixLift 6298082
  have htrace : WordTrace (prefixWord ++ tailWord_6298082) baseStart_6298082 baseEnd_6298082 := by
    simpa [prefixWord, tailWord_6298082, baseEnd_6298082] using wordTrace_append hprefix tailTrace_6298082
  have hstable : (prefixWord ++ tailWord_6298082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298082).length < 2 ^ (prefixWord ++ tailWord_6298082).sum := by decide
  have hdescent : baseEnd_6298082 < baseStart_6298082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298154 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6298154 : Nat := 118140960795 + 6298154 * 2 ^ 59
def prefixEnd_6298154 : Nat := 4983230072969 + 3 ^ 40 * 6298154 * 2
def baseEnd_6298154 : Nat := 3233980238037256677210323

theorem tailTrace_6298154 : CollatzResearch.WordTrace tailWord_6298154 prefixEnd_6298154 3233980238037256677210323 := by
  unfold tailWord_6298154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57428137006217792978077379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153141698683247447941539677 57428137006217792978077379)
  ·
    refine ⟨86142205509326689467116069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57428137006217792978077379 86142205509326689467116069)
    ·
      refine ⟨16151663532998754275084263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86142205509326689467116069 16151663532998754275084263)
      ·
        refine ⟨24227495299498131412626395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151663532998754275084263 24227495299498131412626395)
        ·
          refine ⟨36341242949247197118939593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227495299498131412626395 36341242949247197118939593)
          ·
            refine ⟨27255932211935397839204695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36341242949247197118939593 27255932211935397839204695)
            ·
              refine ⟨40883898317903096758807043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27255932211935397839204695 40883898317903096758807043)
              ·
                refine ⟨61325847476854645138210565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40883898317903096758807043 61325847476854645138210565)
                ·
                  refine ⟨11498596401910245963414481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61325847476854645138210565 11498596401910245963414481)
                  ·
                    refine ⟨8623947301432684472560861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11498596401910245963414481 8623947301432684472560861)
                    ·
                      refine ⟨3233980238037256677210323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623947301432684472560861 3233980238037256677210323)
                      ·
                        rfl

theorem cell23_6298154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6298154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298154 prefixEnd_6298154 := by exact prefixLift 6298154
  have htrace : WordTrace (prefixWord ++ tailWord_6298154) baseStart_6298154 baseEnd_6298154 := by
    simpa [prefixWord, tailWord_6298154, baseEnd_6298154] using wordTrace_append hprefix tailTrace_6298154
  have hstable : (prefixWord ++ tailWord_6298154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298154).length < 2 ^ (prefixWord ++ tailWord_6298154).sum := by decide
  have hdescent : baseEnd_6298154 < baseStart_6298154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298160 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_6298160 : Nat := 118140960795 + 6298160 * 2 ^ 59
def prefixEnd_6298160 : Nat := 4983230072969 + 3 ^ 40 * 6298160 * 2
def baseEnd_6298160 : Nat := 3233983318921183653735295

theorem tailTrace_6298160 : CollatzResearch.WordTrace tailWord_6298160 prefixEnd_6298160 3233983318921183653735295 := by
  unfold tailWord_6298160
  simp only [CollatzResearch.WordTrace]
  refine ⟨114856383431424717468513967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153141844575232956624685289 114856383431424717468513967)
  ·
    refine ⟨172284575147137076202770951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114856383431424717468513967 172284575147137076202770951)
    ·
      refine ⟨258426862720705614304156427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172284575147137076202770951 258426862720705614304156427)
      ·
        refine ⟨387640294081058421456234641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258426862720705614304156427 387640294081058421456234641)
        ·
          refine ⟨290730220560793816092175981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387640294081058421456234641 290730220560793816092175981)
          ·
            refine ⟨109023832710297681034565993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290730220560793816092175981 109023832710297681034565993)
            ·
              refine ⟨81767874532723260775924495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109023832710297681034565993 81767874532723260775924495)
              ·
                refine ⟨122651811799084891163886743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81767874532723260775924495 122651811799084891163886743)
                ·
                  refine ⟨183977717698627336745830115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122651811799084891163886743 183977717698627336745830115)
                  ·
                    refine ⟨275966576547941005118745173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 183977717698627336745830115 275966576547941005118745173)
                    ·
                      refine ⟨3233983318921183653735295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 275966576547941005118745173 3233983318921183653735295)
                      ·
                        rfl

theorem cell23_6298160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_6298160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298160 prefixEnd_6298160 := by exact prefixLift 6298160
  have htrace : WordTrace (prefixWord ++ tailWord_6298160) baseStart_6298160 baseEnd_6298160 := by
    simpa [prefixWord, tailWord_6298160, baseEnd_6298160] using wordTrace_append hprefix tailTrace_6298160
  have hstable : (prefixWord ++ tailWord_6298160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298160).length < 2 ^ (prefixWord ++ tailWord_6298160).sum := by decide
  have hdescent : baseEnd_6298160 < baseStart_6298160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298184 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_6298184 : Nat := 118140960795 + 6298184 * 2 ^ 59
def prefixEnd_6298184 : Nat := 4983230072969 + 3 ^ 40 * 6298184 * 2
def baseEnd_6298184 : Nat := 3233995642456891559835185

theorem tailTrace_6298184 : CollatzResearch.WordTrace tailWord_6298184 prefixEnd_6298184 3233995642456891559835185 := by
  unfold tailWord_6298184
  simp only [CollatzResearch.WordTrace]
  refine ⟨114856821107381243517950803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153142428143174991357267737 114856821107381243517950803)
  ·
    refine ⟨172285231661071865276926205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114856821107381243517950803 172285231661071865276926205)
    ·
      refine ⟨64606961872901949478847327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172285231661071865276926205 64606961872901949478847327)
      ·
        refine ⟨96910442809352924218270991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64606961872901949478847327 96910442809352924218270991)
        ·
          refine ⟨145365664214029386327406487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96910442809352924218270991 145365664214029386327406487)
          ·
            refine ⟨218048496321044079491109731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145365664214029386327406487 218048496321044079491109731)
            ·
              refine ⟨327072744481566119236664597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218048496321044079491109731 327072744481566119236664597)
              ·
                refine ⟨15331534897573411839218653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327072744481566119236664597 15331534897573411839218653)
                ·
                  refine ⟨5749325586590029439706995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15331534897573411839218653 5749325586590029439706995)
                  ·
                    refine ⟨8623988379885044159560493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5749325586590029439706995 8623988379885044159560493)
                    ·
                      refine ⟨3233995642456891559835185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8623988379885044159560493 3233995642456891559835185)
                      ·
                        rfl

theorem cell23_6298184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_6298184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298184 prefixEnd_6298184 := by exact prefixLift 6298184
  have htrace : WordTrace (prefixWord ++ tailWord_6298184) baseStart_6298184 baseEnd_6298184 := by
    simpa [prefixWord, tailWord_6298184, baseEnd_6298184] using wordTrace_append hprefix tailTrace_6298184
  have hstable : (prefixWord ++ tailWord_6298184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298184).length < 2 ^ (prefixWord ++ tailWord_6298184).sum := by decide
  have hdescent : baseEnd_6298184 < baseStart_6298184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298218 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_6298218 : Nat := 118140960795 + 6298218 * 2 ^ 59
def prefixEnd_6298218 : Nat := 4983230072969 + 3 ^ 40 * 6298218 * 2
def baseEnd_6298218 : Nat := 3234013100799144426810029

theorem tailTrace_6298218 : CollatzResearch.WordTrace tailWord_6298218 prefixEnd_6298218 3234013100799144426810029 := by
  unfold tailWord_6298218
  simp only [CollatzResearch.WordTrace]
  refine ⟨57428720574159827710659827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153143254864426207228426205 57428720574159827710659827)
  ·
    refine ⟨86143080861239741565989741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57428720574159827710659827 86143080861239741565989741)
    ·
      refine ⟨32303655322964903087246153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86143080861239741565989741 32303655322964903087246153)
      ·
        refine ⟨24227741492223677315434615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32303655322964903087246153 24227741492223677315434615)
        ·
          refine ⟨36341612238335515973151923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227741492223677315434615 36341612238335515973151923)
          ·
            refine ⟨54512418357503273959727885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36341612238335515973151923 54512418357503273959727885)
            ·
              refine ⟨20442156884063727734897957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54512418357503273959727885 20442156884063727734897957)
              ·
                refine ⟨3832904415761948950293367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20442156884063727734897957 3832904415761948950293367)
                ·
                  refine ⟨5749356623642923425440051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832904415761948950293367 5749356623642923425440051)
                  ·
                    refine ⟨8624034935464385138160077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5749356623642923425440051 8624034935464385138160077)
                    ·
                      refine ⟨3234013100799144426810029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8624034935464385138160077 3234013100799144426810029)
                      ·
                        rfl

theorem cell23_6298218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_6298218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298218 prefixEnd_6298218 := by exact prefixLift 6298218
  have htrace : WordTrace (prefixWord ++ tailWord_6298218) baseStart_6298218 baseEnd_6298218 := by
    simpa [prefixWord, tailWord_6298218, baseEnd_6298218] using wordTrace_append hprefix tailTrace_6298218
  have hstable : (prefixWord ++ tailWord_6298218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298218).length < 2 ^ (prefixWord ++ tailWord_6298218).sum := by decide
  have hdescent : baseEnd_6298218 < baseStart_6298218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298254 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6298254 : Nat := 118140960795 + 6298254 * 2 ^ 59
def prefixEnd_6298254 : Nat := 4983230072969 + 3 ^ 40 * 6298254 * 2
def baseEnd_6298254 : Nat := 3234031586102706285959863

theorem tailTrace_6298254 : CollatzResearch.WordTrace tailWord_6298254 prefixEnd_6298254 3234031586102706285959863 := by
  unfold tailWord_6298254
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714524415563611123868727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153144130216339259327299877 28714524415563611123868727)
  ·
    refine ⟨43071786623345416685803091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28714524415563611123868727 43071786623345416685803091)
    ·
      refine ⟨64607679935018125028704637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43071786623345416685803091 64607679935018125028704637)
      ·
        refine ⟨24227879975631796885764239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64607679935018125028704637 24227879975631796885764239)
        ·
          refine ⟨36341819963447695328646359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227879975631796885764239 36341819963447695328646359)
          ·
            refine ⟨54512729945171542992969539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36341819963447695328646359 54512729945171542992969539)
            ·
              refine ⟨81769094917757314489454309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54512729945171542992969539 81769094917757314489454309)
              ·
                refine ⟨15331705297079496466772683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81769094917757314489454309 15331705297079496466772683)
                ·
                  refine ⟨22997557945619244700159025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15331705297079496466772683 22997557945619244700159025)
                  ·
                    refine ⟨17248168459214433525119269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22997557945619244700159025 17248168459214433525119269)
                    ·
                      refine ⟨3234031586102706285959863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17248168459214433525119269 3234031586102706285959863)
                      ·
                        rfl

theorem cell23_6298254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6298254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298254 prefixEnd_6298254 := by exact prefixLift 6298254
  have htrace : WordTrace (prefixWord ++ tailWord_6298254) baseStart_6298254 baseEnd_6298254 := by
    simpa [prefixWord, tailWord_6298254, baseEnd_6298254] using wordTrace_append hprefix tailTrace_6298254
  have hstable : (prefixWord ++ tailWord_6298254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298254).length < 2 ^ (prefixWord ++ tailWord_6298254).sum := by decide
  have hdescent : baseEnd_6298254 < baseStart_6298254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298257 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_6298257 : Nat := 118140960795 + 6298257 * 2 ^ 59
def prefixEnd_6298257 : Nat := 4983230072969 + 3 ^ 40 * 6298257 * 2
def baseEnd_6298257 : Nat := 3234033126544669774222349

theorem tailTrace_6298257 : CollatzResearch.WordTrace tailWord_6298257 prefixEnd_6298257 3234033126544669774222349 := by
  unfold tailWord_6298257
  simp only [CollatzResearch.WordTrace]
  refine ⟨229716304743498020503309025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153144203162332013668872683 229716304743498020503309025)
  ·
    refine ⟨172287228557623515377481769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229716304743498020503309025 172287228557623515377481769)
    ·
      refine ⟨129215421418217636533111327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172287228557623515377481769 129215421418217636533111327)
      ·
        refine ⟨193823132127326454799666991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129215421418217636533111327 193823132127326454799666991)
        ·
          refine ⟨290734698190989682199500487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193823132127326454799666991 290734698190989682199500487)
          ·
            refine ⟨436102047286484523299250731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290734698190989682199500487 436102047286484523299250731)
            ·
              refine ⟨654153070929726784948876097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436102047286484523299250731 654153070929726784948876097)
              ·
                refine ⟨490614803197295088711657073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654153070929726784948876097 490614803197295088711657073)
                ·
                  refine ⟨367961102397971316533742805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490614803197295088711657073 367961102397971316533742805)
                  ·
                    refine ⟨8624088337452452731259597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 367961102397971316533742805 8624088337452452731259597)
                    ·
                      refine ⟨3234033126544669774222349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8624088337452452731259597 3234033126544669774222349)
                      ·
                        rfl

theorem cell23_6298257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_6298257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298257 prefixEnd_6298257 := by exact prefixLift 6298257
  have htrace : WordTrace (prefixWord ++ tailWord_6298257) baseStart_6298257 baseEnd_6298257 := by
    simpa [prefixWord, tailWord_6298257, baseEnd_6298257] using wordTrace_append hprefix tailTrace_6298257
  have hstable : (prefixWord ++ tailWord_6298257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298257).length < 2 ^ (prefixWord ++ tailWord_6298257).sum := by decide
  have hdescent : baseEnd_6298257 < baseStart_6298257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298258 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_6298258 : Nat := 118140960795 + 6298258 * 2 ^ 59
def prefixEnd_6298258 : Nat := 4983230072969 + 3 ^ 40 * 6298258 * 2
def baseEnd_6298258 : Nat := 3234033640025324270309845

theorem tailTrace_6298258 : CollatzResearch.WordTrace tailWord_6298258 prefixEnd_6298258 3234033640025324270309845 := by
  unfold tailWord_6298258
  simp only [CollatzResearch.WordTrace]
  refine ⟨57429085304123599418523857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153144227477662931782730285 57429085304123599418523857)
  ·
    refine ⟨43071813978092699563892893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57429085304123599418523857 43071813978092699563892893)
    ·
      refine ⟨16151930241784762336459835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43071813978092699563892893 16151930241784762336459835)
      ·
        refine ⟨24227895362677143504689753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151930241784762336459835 24227895362677143504689753)
        ·
          refine ⟨18170921522007857628517315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24227895362677143504689753 18170921522007857628517315)
          ·
            refine ⟨27256382283011786442775973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18170921522007857628517315 27256382283011786442775973)
            ·
              refine ⟨5110571678064709958020495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27256382283011786442775973 5110571678064709958020495)
              ·
                refine ⟨7665857517097064937030743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110571678064709958020495 7665857517097064937030743)
                ·
                  refine ⟨11498786275645597405546115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7665857517097064937030743 11498786275645597405546115)
                  ·
                    refine ⟨17248179413468396108319173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11498786275645597405546115 17248179413468396108319173)
                    ·
                      refine ⟨3234033640025324270309845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17248179413468396108319173 3234033640025324270309845)
                      ·
                        rfl

theorem cell23_6298258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_6298258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298258 prefixEnd_6298258 := by exact prefixLift 6298258
  have htrace : WordTrace (prefixWord ++ tailWord_6298258) baseStart_6298258 baseEnd_6298258 := by
    simpa [prefixWord, tailWord_6298258, baseEnd_6298258] using wordTrace_append hprefix tailTrace_6298258
  have hstable : (prefixWord ++ tailWord_6298258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298258).length < 2 ^ (prefixWord ++ tailWord_6298258).sum := by decide
  have hdescent : baseEnd_6298258 < baseStart_6298258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298268 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_6298268 : Nat := 118140960795 + 6298268 * 2 ^ 59
def prefixEnd_6298268 : Nat := 4983230072969 + 3 ^ 40 * 6298268 * 2
def baseEnd_6298268 : Nat := 1078012924943956410394933

theorem tailTrace_6298268 : CollatzResearch.WordTrace tailWord_6298268 prefixEnd_6298268 1078012924943956410394933 := by
  unfold tailWord_6298268
  simp only [CollatzResearch.WordTrace]
  refine ⟨114858352973229084690979729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153144470630972112921306305 114858352973229084690979729)
  ·
    refine ⟨86143764729921813518234797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114858352973229084690979729 86143764729921813518234797)
    ·
      refine ⟨32303911773720680069338049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86143764729921813518234797 32303911773720680069338049)
      ·
        refine ⟨24227933830290510052003537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32303911773720680069338049 24227933830290510052003537)
        ·
          refine ⟨18170950372717882539002653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24227933830290510052003537 18170950372717882539002653)
          ·
            refine ⟨6814106389769205952125995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18170950372717882539002653 6814106389769205952125995)
            ·
              refine ⟨10221159584653808928188993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814106389769205952125995 10221159584653808928188993)
              ·
                refine ⟨7665869688490356696141745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10221159584653808928188993 7665869688490356696141745)
                ·
                  refine ⟨5749402266367767522106309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7665869688490356696141745 5749402266367767522106309)
                  ·
                    refine ⟨1078012924943956410394933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749402266367767522106309 1078012924943956410394933)
                    ·
                      rfl

theorem cell23_6298268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_6298268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298268 prefixEnd_6298268 := by exact prefixLift 6298268
  have htrace : WordTrace (prefixWord ++ tailWord_6298268) baseStart_6298268 baseEnd_6298268 := by
    simpa [prefixWord, tailWord_6298268, baseEnd_6298268] using wordTrace_append hprefix tailTrace_6298268
  have hstable : (prefixWord ++ tailWord_6298268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298268).length < 2 ^ (prefixWord ++ tailWord_6298268).sum := by decide
  have hdescent : baseEnd_6298268 < baseStart_6298268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298291 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 3]
def baseStart_6298291 : Nat := 118140960795 + 6298291 * 2 ^ 59
def prefixEnd_6298291 : Nat := 4983230072969 + 3 ^ 40 * 6298291 * 2
def baseEnd_6298291 : Nat := 3234050584886922641197193

theorem tailTrace_6298291 : CollatzResearch.WordTrace tailWord_6298291 prefixEnd_6298291 3234050584886922641197193 := by
  unfold tailWord_6298291
  simp only [CollatzResearch.WordTrace]
  refine ⟨229717544825374844310046727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153145029883583229540031151 229717544825374844310046727)
  ·
    refine ⟨344576317238062266465070091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229717544825374844310046727 344576317238062266465070091)
    ·
      refine ⟨516864475857093399697605137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344576317238062266465070091 516864475857093399697605137)
      ·
        refine ⟨387648356892820049773203853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516864475857093399697605137 387648356892820049773203853)
        ·
          refine ⟨145368133834807518664951445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387648356892820049773203853 145368133834807518664951445)
          ·
            refine ⟨6814131273506602437419599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145368133834807518664951445 6814131273506602437419599)
            ·
              refine ⟨10221196910259903656129399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814131273506602437419599 10221196910259903656129399)
              ·
                refine ⟨15331795365389855484194099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10221196910259903656129399 15331795365389855484194099)
                ·
                  refine ⟨22997693048084783226291149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15331795365389855484194099 22997693048084783226291149)
                  ·
                    refine ⟨8624134893031793709859181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22997693048084783226291149 8624134893031793709859181)
                    ·
                      refine ⟨3234050584886922641197193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8624134893031793709859181 3234050584886922641197193)
                      ·
                        rfl

theorem cell23_6298291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_6298291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298291 prefixEnd_6298291 := by exact prefixLift 6298291
  have htrace : WordTrace (prefixWord ++ tailWord_6298291) baseStart_6298291 baseEnd_6298291 := by
    simpa [prefixWord, tailWord_6298291, baseEnd_6298291] using wordTrace_append hprefix tailTrace_6298291
  have hstable : (prefixWord ++ tailWord_6298291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298291).length < 2 ^ (prefixWord ++ tailWord_6298291).sum := by decide
  have hdescent : baseEnd_6298291 < baseStart_6298291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298318 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_6298318 : Nat := 118140960795 + 6298318 * 2 ^ 59
def prefixEnd_6298318 : Nat := 4983230072969 + 3 ^ 40 * 6298318 * 2
def baseEnd_6298318 : Nat := 3234064448864594035559569

theorem tailTrace_6298318 : CollatzResearch.WordTrace tailWord_6298318 prefixEnd_6298318 3234064448864594035559569 := by
  unfold tailWord_6298318
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714816199534628490159951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153145686397518018614186405 28714816199534628490159951)
  ·
    refine ⟨43072224299301942735239927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28714816199534628490159951 43072224299301942735239927)
    ·
      refine ⟨64608336448952914102859891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43072224299301942735239927 64608336448952914102859891)
      ·
        refine ⟨96912504673429371154289837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64608336448952914102859891 96912504673429371154289837)
        ·
          refine ⟨36342189252536014182858689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96912504673429371154289837 36342189252536014182858689)
          ·
            refine ⟨27256641939402010637144017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36342189252536014182858689 27256641939402010637144017)
            ·
              refine ⟨20442481454551507977858013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27256641939402010637144017 20442481454551507977858013)
              ·
                refine ⟨7665930545456815491696755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20442481454551507977858013 7665930545456815491696755)
                ·
                  refine ⟨11498895818185223237545133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7665930545456815491696755 11498895818185223237545133)
                  ·
                    refine ⟨4312085931819458714079425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11498895818185223237545133 4312085931819458714079425)
                    ·
                      refine ⟨3234064448864594035559569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312085931819458714079425 3234064448864594035559569)
                      ·
                        rfl

theorem cell23_6298318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_6298318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298318 prefixEnd_6298318 := by exact prefixLift 6298318
  have htrace : WordTrace (prefixWord ++ tailWord_6298318) baseStart_6298318 baseEnd_6298318 := by
    simpa [prefixWord, tailWord_6298318, baseEnd_6298318] using wordTrace_append hprefix tailTrace_6298318
  have hstable : (prefixWord ++ tailWord_6298318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298318).length < 2 ^ (prefixWord ++ tailWord_6298318).sum := by decide
  have hdescent : baseEnd_6298318 < baseStart_6298318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298394 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_6298394 : Nat := 118140960795 + 6298394 * 2 ^ 59
def prefixEnd_6298394 : Nat := 4983230072969 + 3 ^ 40 * 6298394 * 2
def baseEnd_6298394 : Nat := 3234103473394335738209219

theorem tailTrace_6298394 : CollatzResearch.WordTrace tailWord_6298394 prefixEnd_6298394 3234103473394335738209219 := by
  unfold tailWord_6298394
  simp only [CollatzResearch.WordTrace]
  refine ⟨57430325386000423225261559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153147534362667795267364157 57430325386000423225261559)
  ·
    refine ⟨86145488079000634837892339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57430325386000423225261559 86145488079000634837892339)
    ·
      refine ⟨129218232118500952256838509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86145488079000634837892339 129218232118500952256838509)
      ·
        refine ⟨48456837044437857096314441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129218232118500952256838509 48456837044437857096314441)
        ·
          refine ⟨36342627783328392822235831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48456837044437857096314441 36342627783328392822235831)
          ·
            refine ⟨54513941674992589233353747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36342627783328392822235831 54513941674992589233353747)
            ·
              refine ⟨81770912512488883850030621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54513941674992589233353747 81770912512488883850030621)
              ·
                refine ⟨30664092192183331443761483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81770912512488883850030621 30664092192183331443761483)
                ·
                  refine ⟨45996138288274997165642225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30664092192183331443761483 45996138288274997165642225)
                  ·
                    refine ⟨34497103716206247874231669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45996138288274997165642225 34497103716206247874231669)
                    ·
                      refine ⟨3234103473394335738209219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34497103716206247874231669 3234103473394335738209219)
                      ·
                        rfl

theorem cell23_6298394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_6298394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298394 prefixEnd_6298394 := by exact prefixLift 6298394
  have htrace : WordTrace (prefixWord ++ tailWord_6298394) baseStart_6298394 baseEnd_6298394 := by
    simpa [prefixWord, tailWord_6298394, baseEnd_6298394] using wordTrace_append hprefix tailTrace_6298394
  have hstable : (prefixWord ++ tailWord_6298394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298394).length < 2 ^ (prefixWord ++ tailWord_6298394).sum := by decide
  have hdescent : baseEnd_6298394 < baseStart_6298394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298421 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6298421 : Nat := 118140960795 + 6298421 * 2 ^ 59
def prefixEnd_6298421 : Nat := 4983230072969 + 3 ^ 40 * 6298421 * 2
def baseEnd_6298421 : Nat := 3234117337372007132571595

theorem tailTrace_6298421 : CollatzResearch.WordTrace tailWord_6298421 prefixEnd_6298421 3234117337372007132571595 := by
  unfold tailWord_6298421
  simp only [CollatzResearch.WordTrace]
  refine ⟨229722286314903876512279117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153148190876602584341519411 229722286314903876512279117)
  ·
    refine ⟨86145857368088953692104669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229722286314903876512279117 86145857368088953692104669)
    ·
      refine ⟨32304696513033357634539251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86145857368088953692104669 32304696513033357634539251)
      ·
        refine ⟨48457044769550036451808877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32304696513033357634539251 48457044769550036451808877)
        ·
          refine ⟨18171391788581263669428329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48457044769550036451808877 18171391788581263669428329)
          ·
            refine ⟨13628543841435947752071247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18171391788581263669428329 13628543841435947752071247)
            ·
              refine ⟨20442815762153921628106871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13628543841435947752071247 20442815762153921628106871)
              ·
                refine ⟨30664223643230882442160307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20442815762153921628106871 30664223643230882442160307)
                ·
                  refine ⟨45996335464846323663240461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30664223643230882442160307 45996335464846323663240461)
                  ·
                    refine ⟨17248625799317371373715173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45996335464846323663240461 17248625799317371373715173)
                    ·
                      refine ⟨3234117337372007132571595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17248625799317371373715173 3234117337372007132571595)
                      ·
                        rfl

theorem cell23_6298421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6298421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298421 prefixEnd_6298421 := by exact prefixLift 6298421
  have htrace : WordTrace (prefixWord ++ tailWord_6298421) baseStart_6298421 baseEnd_6298421 := by
    simpa [prefixWord, tailWord_6298421, baseEnd_6298421] using wordTrace_append hprefix tailTrace_6298421
  have hstable : (prefixWord ++ tailWord_6298421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298421).length < 2 ^ (prefixWord ++ tailWord_6298421).sum := by decide
  have hdescent : baseEnd_6298421 < baseStart_6298421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298448 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 1, 4]
def baseStart_6298448 : Nat := 118140960795 + 6298448 * 2 ^ 59
def prefixEnd_6298448 : Nat := 4983230072969 + 3 ^ 40 * 6298448 * 2
def baseEnd_6298448 : Nat := 1078043733783226175644657

theorem tailTrace_6298448 : CollatzResearch.WordTrace tailWord_6298448 prefixEnd_6298448 1078043733783226175644657 := by
  unfold tailWord_6298448
  simp only [CollatzResearch.WordTrace]
  refine ⟨114861635542903030061755999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153148847390537373415674665 114861635542903030061755999)
  ·
    refine ⟨172292453314354545092633999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114861635542903030061755999 172292453314354545092633999)
    ·
      refine ⟨258438679971531817638950999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172292453314354545092633999 258438679971531817638950999)
      ·
        refine ⟨387658019957297726458426499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258438679971531817638950999 387658019957297726458426499)
        ·
          refine ⟨581487029935946589687639749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387658019957297726458426499 581487029935946589687639749)
          ·
            refine ⟨109028818112989985566432453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 581487029935946589687639749 109028818112989985566432453)
            ·
              refine ⟨20442903396185622293706085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109028818112989985566432453 20442903396185622293706085)
              ·
                refine ⟨3833044386784804180069891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20442903396185622293706085 3833044386784804180069891)
                ·
                  refine ⟨5749566580177206270104837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833044386784804180069891 5749566580177206270104837)
                  ·
                    refine ⟨1078043733783226175644657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749566580177206270104837 1078043733783226175644657)
                    ·
                      rfl

theorem cell23_6298448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 4].length) (baseStart_6298448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298448 prefixEnd_6298448 := by exact prefixLift 6298448
  have htrace : WordTrace (prefixWord ++ tailWord_6298448) baseStart_6298448 baseEnd_6298448 := by
    simpa [prefixWord, tailWord_6298448, baseEnd_6298448] using wordTrace_append hprefix tailTrace_6298448
  have hstable : (prefixWord ++ tailWord_6298448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298448).length < 2 ^ (prefixWord ++ tailWord_6298448).sum := by decide
  have hdescent : baseEnd_6298448 < baseStart_6298448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298464 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6298464 : Nat := 118140960795 + 6298464 * 2 ^ 59
def prefixEnd_6298464 : Nat := 4983230072969 + 3 ^ 40 * 6298464 * 2
def baseEnd_6298464 : Nat := 3234139417040150464333897

theorem tailTrace_6298464 : CollatzResearch.WordTrace tailWord_6298464 prefixEnd_6298464 3234139417040150464333897 := by
  unfold tailWord_6298464
  simp only [CollatzResearch.WordTrace]
  refine ⟨114861927326874047428047223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153149236435832063237396297 114861927326874047428047223)
  ·
    refine ⟨172292890990311071142070835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114861927326874047428047223 172292890990311071142070835)
    ·
      refine ⟨258439336485466606713106253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172292890990311071142070835 258439336485466606713106253)
      ·
        refine ⟨96914751182049977517414845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258439336485466606713106253 96914751182049977517414845)
        ·
          refine ⟨36343031693268741569030567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96914751182049977517414845 36343031693268741569030567)
          ·
            refine ⟨54514547539903112353545851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36343031693268741569030567 54514547539903112353545851)
            ·
              refine ⟨81771821309854668530318777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54514547539903112353545851 81771821309854668530318777)
              ·
                refine ⟨61328865982391001397739083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81771821309854668530318777 61328865982391001397739083)
                ·
                  refine ⟨91993298973586502096608625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61328865982391001397739083 91993298973586502096608625)
                  ·
                    refine ⟨68994974230189876572456469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91993298973586502096608625 68994974230189876572456469)
                    ·
                      refine ⟨3234139417040150464333897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68994974230189876572456469 3234139417040150464333897)
                      ·
                        rfl

theorem cell23_6298464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6298464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298464 prefixEnd_6298464 := by exact prefixLift 6298464
  have htrace : WordTrace (prefixWord ++ tailWord_6298464) baseStart_6298464 baseEnd_6298464 := by
    simpa [prefixWord, tailWord_6298464, baseEnd_6298464] using wordTrace_append hprefix tailTrace_6298464
  have hstable : (prefixWord ++ tailWord_6298464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298464).length < 2 ^ (prefixWord ++ tailWord_6298464).sum := by decide
  have hdescent : baseEnd_6298464 < baseStart_6298464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298491 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 1, 5]
def baseStart_6298491 : Nat := 118140960795 + 6298491 * 2 ^ 59
def prefixEnd_6298491 : Nat := 4983230072969 + 3 ^ 40 * 6298491 * 2
def baseEnd_6298491 : Nat := 1078051093672607286232091

theorem tailTrace_6298491 : CollatzResearch.WordTrace tailWord_6298491 prefixEnd_6298491 1078051093672607286232091 := by
  unfold tailWord_6298491
  simp only [CollatzResearch.WordTrace]
  refine ⟨229724839424650278467327327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153149892949766852311551551 229724839424650278467327327)
  ·
    refine ⟨344587259136975417700990991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229724839424650278467327327 344587259136975417700990991)
    ·
      refine ⟨516880888705463126551486487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344587259136975417700990991 516880888705463126551486487)
      ·
        refine ⟨775321333058194689827229731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516880888705463126551486487 775321333058194689827229731)
        ·
          refine ⟨1162981999587292034740844597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775321333058194689827229731 1162981999587292034740844597)
          ·
            refine ⟨109029562461308628256954181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1162981999587292034740844597 109029562461308628256954181)
            ·
              refine ⟨20443042961495367798178909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109029562461308628256954181 20443042961495367798178909)
              ·
                refine ⟨7666141110560762924317091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20443042961495367798178909 7666141110560762924317091)
                ·
                  refine ⟨11499211665841144386475637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7666141110560762924317091 11499211665841144386475637)
                  ·
                    refine ⟨1078051093672607286232091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11499211665841144386475637 1078051093672607286232091)
                    ·
                      rfl

theorem cell23_6298491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 5].length) (baseStart_6298491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298491 prefixEnd_6298491 := by exact prefixLift 6298491
  have htrace : WordTrace (prefixWord ++ tailWord_6298491) baseStart_6298491 baseEnd_6298491 := by
    simpa [prefixWord, tailWord_6298491, baseEnd_6298491] using wordTrace_append hprefix tailTrace_6298491
  have hstable : (prefixWord ++ tailWord_6298491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298491).length < 2 ^ (prefixWord ++ tailWord_6298491).sum := by decide
  have hdescent : baseEnd_6298491 < baseStart_6298491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298505 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 3]
def baseStart_6298505 : Nat := 118140960795 + 6298505 * 2 ^ 59
def prefixEnd_6298505 : Nat := 4983230072969 + 3 ^ 40 * 6298505 * 2
def baseEnd_6298505 : Nat := 3234160469746984803921209

theorem tailTrace_6298505 : CollatzResearch.WordTrace tailWord_6298505 prefixEnd_6298505 3234160469746984803921209 := by
  unfold tailWord_6298505
  simp only [CollatzResearch.WordTrace]
  refine ⟨229725350046599558858336969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153150233364399705905557979 229725350046599558858336969)
  ·
    refine ⟨172294012534949669143752727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229725350046599558858336969 172294012534949669143752727)
    ·
      refine ⟨258441018802424503715629091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172294012534949669143752727 258441018802424503715629091)
      ·
        refine ⟨387661528203636755573443637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258441018802424503715629091 387661528203636755573443637)
        ·
          refine ⟨36343268269090945835010341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 387661528203636755573443637 36343268269090945835010341)
          ·
            refine ⟨6814362800454552344064439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36343268269090945835010341 6814362800454552344064439)
            ·
              refine ⟨10221544200681828516096659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814362800454552344064439 10221544200681828516096659)
              ·
                refine ⟨15332316301022742774144989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10221544200681828516096659 15332316301022742774144989)
                ·
                  refine ⟨5749618612883528540304371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15332316301022742774144989 5749618612883528540304371)
                  ·
                    refine ⟨8624427919325292810456557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5749618612883528540304371 8624427919325292810456557)
                    ·
                      refine ⟨3234160469746984803921209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8624427919325292810456557 3234160469746984803921209)
                      ·
                        rfl

theorem cell23_6298505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_6298505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298505 prefixEnd_6298505 := by exact prefixLift 6298505
  have htrace : WordTrace (prefixWord ++ tailWord_6298505) baseStart_6298505 baseEnd_6298505 := by
    simpa [prefixWord, tailWord_6298505, baseEnd_6298505] using wordTrace_append hprefix tailTrace_6298505
  have hstable : (prefixWord ++ tailWord_6298505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298505).length < 2 ^ (prefixWord ++ tailWord_6298505).sum := by decide
  have hdescent : baseEnd_6298505 < baseStart_6298505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298528 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_6298528 : Nat := 118140960795 + 6298528 * 2 ^ 59
def prefixEnd_6298528 : Nat := 4983230072969 + 3 ^ 40 * 6298528 * 2
def baseEnd_6298528 : Nat := 3234172279802038213933603

theorem tailTrace_6298528 : CollatzResearch.WordTrace tailWord_6298528 prefixEnd_6298528 3234172279802038213933603 := by
  unfold tailWord_6298528
  simp only [CollatzResearch.WordTrace]
  refine ⟨114863094462758116893212119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153150792617010822524282825 114863094462758116893212119)
  ·
    refine ⟨172294641694137175339818179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114863094462758116893212119 172294641694137175339818179)
    ·
      refine ⟨258441962541205763009727269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172294641694137175339818179 258441962541205763009727269)
      ·
        refine ⟨48457867976476080564323863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258441962541205763009727269 48457867976476080564323863)
        ·
          refine ⟨72686801964714120846485795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48457867976476080564323863 72686801964714120846485795)
          ·
            refine ⟨109030202947071181269728693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72686801964714120846485795 109030202947071181269728693)
            ·
              refine ⟨10221581526287923244037065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109030202947071181269728693 10221581526287923244037065)
              ·
                refine ⟨7666186144715942433027799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10221581526287923244037065 7666186144715942433027799)
                ·
                  refine ⟨11499279217073913649541699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7666186144715942433027799 11499279217073913649541699)
                  ·
                    refine ⟨17248918825610870474312549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11499279217073913649541699 17248918825610870474312549)
                    ·
                      refine ⟨3234172279802038213933603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17248918825610870474312549 3234172279802038213933603)
                      ·
                        rfl

theorem cell23_6298528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_6298528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298528 prefixEnd_6298528 := by exact prefixLift 6298528
  have htrace : WordTrace (prefixWord ++ tailWord_6298528) baseStart_6298528 baseEnd_6298528 := by
    simpa [prefixWord, tailWord_6298528, baseEnd_6298528] using wordTrace_append hprefix tailTrace_6298528
  have hstable : (prefixWord ++ tailWord_6298528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298528).length < 2 ^ (prefixWord ++ tailWord_6298528).sum := by decide
  have hdescent : baseEnd_6298528 < baseStart_6298528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298550 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6298550 : Nat := 118140960795 + 6298550 * 2 ^ 59
def prefixEnd_6298550 : Nat := 4983230072969 + 3 ^ 40 * 6298550 * 2
def baseEnd_6298550 : Nat := 1078061192125479042619501

theorem tailTrace_6298550 : CollatzResearch.WordTrace tailWord_6298550 prefixEnd_6298550 1078061192125479042619501 := by
  unfold tailWord_6298550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357936958214783221482819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153151327554291021029150069 14357936958214783221482819)
  ·
    refine ⟨21536905437322174832224229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14357936958214783221482819 21536905437322174832224229)
    ·
      refine ⟨4038169769497907781042043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21536905437322174832224229 4038169769497907781042043)
      ·
        refine ⟨6057254654246861671563065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038169769497907781042043 6057254654246861671563065)
        ·
          refine ⟨4542940990685146253672299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6057254654246861671563065 4542940990685146253672299)
          ·
            refine ⟨6814411486027719380508449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542940990685146253672299 6814411486027719380508449)
            ·
              refine ⟨5110808614520789535381337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814411486027719380508449 5110808614520789535381337)
              ·
                refine ⟨3833106460890592151536003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110808614520789535381337 3833106460890592151536003)
                ·
                  refine ⟨5749659691335888227304005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833106460890592151536003 5749659691335888227304005)
                  ·
                    refine ⟨1078061192125479042619501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749659691335888227304005 1078061192125479042619501)
                    ·
                      rfl

theorem cell23_6298550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6298550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298550 prefixEnd_6298550 := by exact prefixLift 6298550
  have htrace : WordTrace (prefixWord ++ tailWord_6298550) baseStart_6298550 baseEnd_6298550 := by
    simpa [prefixWord, tailWord_6298550, baseEnd_6298550] using wordTrace_append hprefix tailTrace_6298550
  have hstable : (prefixWord ++ tailWord_6298550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298550).length < 2 ^ (prefixWord ++ tailWord_6298550).sum := by decide
  have hdescent : baseEnd_6298550 < baseStart_6298550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298568 : List Nat := [2, 1, 3, 1, 5, 2, 1, 8]
def baseStart_6298568 : Nat := 118140960795 + 6298568 * 2 ^ 59
def prefixEnd_6298568 : Nat := 4983230072969 + 3 ^ 40 * 6298568 * 2
def baseEnd_6298568 : Nat := 119784919223267335460497

theorem tailTrace_6298568 : CollatzResearch.WordTrace tailWord_6298568 prefixEnd_6298568 119784919223267335460497 := by
  unfold tailWord_6298568
  simp only [CollatzResearch.WordTrace]
  refine ⟨114863823922685660308940179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153151765230247547078586905 114863823922685660308940179)
  ·
    refine ⟨172295735884028490463410269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114863823922685660308940179 172295735884028490463410269)
    ·
      refine ⟨64610900956510683923778851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172295735884028490463410269 64610900956510683923778851)
      ·
        refine ⟨96916351434766025885668277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64610900956510683923778851 96916351434766025885668277)
        ·
          refine ⟨9085907947009314926781401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96916351434766025885668277 9085907947009314926781401)
          ·
            refine ⟨6814430960256986195086051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9085907947009314926781401 6814430960256986195086051)
            ·
              refine ⟨10221646440385479292629077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814430960256986195086051 10221646440385479292629077)
              ·
                refine ⟨119784919223267335460497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10221646440385479292629077 119784919223267335460497)
                ·
                  rfl

theorem cell23_6298568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 8].length) (baseStart_6298568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298568 prefixEnd_6298568 := by exact prefixLift 6298568
  have htrace : WordTrace (prefixWord ++ tailWord_6298568) baseStart_6298568 baseEnd_6298568 := by
    simpa [prefixWord, tailWord_6298568, baseEnd_6298568] using wordTrace_append hprefix tailTrace_6298568
  have hstable : (prefixWord ++ tailWord_6298568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298568).length < 2 ^ (prefixWord ++ tailWord_6298568).sum := by decide
  have hdescent : baseEnd_6298568 < baseStart_6298568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298618 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_6298618 : Nat := 118140960795 + 6298618 * 2 ^ 59
def prefixEnd_6298618 : Nat := 4983230072969 + 3 ^ 40 * 6298618 * 2
def baseEnd_6298618 : Nat := 3234218493060942861808189

theorem tailTrace_6298618 : CollatzResearch.WordTrace tailWord_6298618 prefixEnd_6298618 3234218493060942861808189 := by
  unfold tailWord_6298618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57432367873797544789300127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153152980996793452771467005 57432367873797544789300127)
  ·
    refine ⟨86148551810696317183950191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57432367873797544789300127 86148551810696317183950191)
    ·
      refine ⟨129222827716044475775925287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86148551810696317183950191 129222827716044475775925287)
      ·
        refine ⟨193834241574066713663887931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129222827716044475775925287 193834241574066713663887931)
        ·
          refine ⟨290751362361100070495831897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193834241574066713663887931 290751362361100070495831897)
          ·
            refine ⟨218063521770825052871873923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290751362361100070495831897 218063521770825052871873923)
            ·
              refine ⟨327095282656237579307810885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218063521770825052871873923 327095282656237579307810885)
              ·
                refine ⟨61330365498044546120214541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327095282656237579307810885 61330365498044546120214541)
                ·
                  refine ⟨22998887061766704795080453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61330365498044546120214541 22998887061766704795080453)
                  ·
                    refine ⟨4312291324081257149077585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22998887061766704795080453 4312291324081257149077585)
                    ·
                      refine ⟨3234218493060942861808189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312291324081257149077585 3234218493060942861808189)
                      ·
                        rfl

theorem cell23_6298618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_6298618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298618 prefixEnd_6298618 := by exact prefixLift 6298618
  have htrace : WordTrace (prefixWord ++ tailWord_6298618) baseStart_6298618 baseEnd_6298618 := by
    simpa [prefixWord, tailWord_6298618, baseEnd_6298618] using wordTrace_append hprefix tailTrace_6298618
  have hstable : (prefixWord ++ tailWord_6298618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298618).length < 2 ^ (prefixWord ++ tailWord_6298618).sum := by decide
  have hdescent : baseEnd_6298618 < baseStart_6298618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298621 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_6298621 : Nat := 118140960795 + 6298621 * 2 ^ 59
def prefixEnd_6298621 : Nat := 4983230072969 + 3 ^ 40 * 6298621 * 2
def baseEnd_6298621 : Nat := 3234220033502906350070675

theorem tailTrace_6298621 : CollatzResearch.WordTrace tailWord_6298621 prefixEnd_6298621 3234220033502906350070675 := by
  unfold tailWord_6298621
  simp only [CollatzResearch.WordTrace]
  refine ⟨229729580914179310669559717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153153053942786207113039811 229729580914179310669559717)
  ·
    refine ⟨43074296421408620750542447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229729580914179310669559717 43074296421408620750542447)
    ·
      refine ⟨64611444632112931125813671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43074296421408620750542447 64611444632112931125813671)
      ·
        refine ⟨96917166948169396688720507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64611444632112931125813671 96917166948169396688720507)
        ·
          refine ⟨145375750422254095033080761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96917166948169396688720507 145375750422254095033080761)
          ·
            refine ⟨109031812816690571274810571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145375750422254095033080761 109031812816690571274810571)
            ·
              refine ⟨163547719225035856912215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109031812816690571274810571 163547719225035856912215857)
              ·
                refine ⟨122660789418776892684161893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163547719225035856912215857 122660789418776892684161893)
                ·
                  refine ⟨22998898016020667378280355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122660789418776892684161893 22998898016020667378280355)
                  ·
                    refine ⟨34498347024031001067420533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22998898016020667378280355 34498347024031001067420533)
                    ·
                      refine ⟨3234220033502906350070675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34498347024031001067420533 3234220033502906350070675)
                      ·
                        rfl

theorem cell23_6298621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_6298621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298621 prefixEnd_6298621 := by exact prefixLift 6298621
  have htrace : WordTrace (prefixWord ++ tailWord_6298621) baseStart_6298621 baseEnd_6298621 := by
    simpa [prefixWord, tailWord_6298621, baseEnd_6298621] using wordTrace_append hprefix tailTrace_6298621
  have hstable : (prefixWord ++ tailWord_6298621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298621).length < 2 ^ (prefixWord ++ tailWord_6298621).sum := by decide
  have hdescent : baseEnd_6298621 < baseStart_6298621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298635 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 1, 4, 2]
def baseStart_6298635 : Nat := 118140960795 + 6298635 * 2 ^ 59
def prefixEnd_6298635 : Nat := 4983230072969 + 3 ^ 40 * 6298635 * 2
def baseEnd_6298635 : Nat := 3234227222232069295295611

theorem tailTrace_6298635 : CollatzResearch.WordTrace tailWord_6298635 prefixEnd_6298635 3234227222232069295295611 := by
  unfold tailWord_6298635
  simp only [CollatzResearch.WordTrace]
  refine ⟨229730091536128591060569359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153153394357419060707046239 229730091536128591060569359)
  ·
    refine ⟨344595137304192886590854039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229730091536128591060569359 344595137304192886590854039)
    ·
      refine ⟨516892705956289329886281059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344595137304192886590854039 516892705956289329886281059)
      ·
        refine ⟨775339058934433994829421589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516892705956289329886281059 775339058934433994829421589)
        ·
          refine ⟨36344018387551593507629137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 775339058934433994829421589 36344018387551593507629137)
          ·
            refine ⟨27258013790663695130721853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36344018387551593507629137 27258013790663695130721853)
            ·
              refine ⟨10221755171498885674020695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27258013790663695130721853 10221755171498885674020695)
              ·
                refine ⟨15332632757248328511031043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10221755171498885674020695 15332632757248328511031043)
                ·
                  refine ⟨22998949135872492766546565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15332632757248328511031043 22998949135872492766546565)
                  ·
                    refine ⟨4312302962976092393727481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22998949135872492766546565 4312302962976092393727481)
                    ·
                      refine ⟨3234227222232069295295611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312302962976092393727481 3234227222232069295295611)
                      ·
                        rfl

theorem cell23_6298635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4, 2].length) (baseStart_6298635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298635 prefixEnd_6298635 := by exact prefixLift 6298635
  have htrace : WordTrace (prefixWord ++ tailWord_6298635) baseStart_6298635 baseEnd_6298635 := by
    simpa [prefixWord, tailWord_6298635, baseEnd_6298635] using wordTrace_append hprefix tailTrace_6298635
  have hstable : (prefixWord ++ tailWord_6298635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298635).length < 2 ^ (prefixWord ++ tailWord_6298635).sum := by decide
  have hdescent : baseEnd_6298635 < baseStart_6298635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298686 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6298686 : Nat := 118140960795 + 6298686 * 2 ^ 59
def prefixEnd_6298686 : Nat := 4983230072969 + 3 ^ 40 * 6298686 * 2
def baseEnd_6298686 : Nat := 3234253409745448595757877

theorem tailTrace_6298686 : CollatzResearch.WordTrace tailWord_6298686 prefixEnd_6298686 3234253409745448595757877 := by
  unfold tailWord_6298686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716493957367978346334489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153154634439295884513783941 28716493957367978346334489)
  ·
    refine ⟨21537370468025983759750867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28716493957367978346334489 21537370468025983759750867)
    ·
      refine ⟨32306055702038975639626301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537370468025983759750867 32306055702038975639626301)
      ·
        refine ⟨12114770888264615864859863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32306055702038975639626301 12114770888264615864859863)
        ·
          refine ⟨18172156332396923797289795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12114770888264615864859863 18172156332396923797289795)
          ·
            refine ⟨27258234498595385695934693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18172156332396923797289795 27258234498595385695934693)
            ·
              refine ⟨5110918968486634817987755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27258234498595385695934693 5110918968486634817987755)
              ·
                refine ⟨7666378452729952226981633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110918968486634817987755 7666378452729952226981633)
                ·
                  refine ⟨5749783839547464170236225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7666378452729952226981633 5749783839547464170236225)
                  ·
                    refine ⟨4312337879660598127677169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749783839547464170236225 4312337879660598127677169)
                    ·
                      refine ⟨3234253409745448595757877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312337879660598127677169 3234253409745448595757877)
                      ·
                        rfl

theorem cell23_6298686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6298686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298686 prefixEnd_6298686 := by exact prefixLift 6298686
  have htrace : WordTrace (prefixWord ++ tailWord_6298686) baseStart_6298686 baseEnd_6298686 := by
    simpa [prefixWord, tailWord_6298686, baseEnd_6298686] using wordTrace_append hprefix tailTrace_6298686
  have hstable : (prefixWord ++ tailWord_6298686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298686).length < 2 ^ (prefixWord ++ tailWord_6298686).sum := by decide
  have hdescent : baseEnd_6298686 < baseStart_6298686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298708 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6298708 : Nat := 118140960795 + 6298708 * 2 ^ 59
def prefixEnd_6298708 : Nat := 4983230072969 + 3 ^ 40 * 6298708 * 2
def baseEnd_6298708 : Nat := 3234264706319847509682775

theorem tailTrace_6298708 : CollatzResearch.WordTrace tailWord_6298708 prefixEnd_6298708 3234264706319847509682775 := by
  unfold tailWord_6298708
  simp only [CollatzResearch.WordTrace]
  refine ⟨114866377032432062263988389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153155169376576083018651185 114866377032432062263988389)
  ·
    refine ⟨21537445693581011674497823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114866377032432062263988389 21537445693581011674497823)
    ·
      refine ⟨32306168540371517511746735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537445693581011674497823 32306168540371517511746735)
      ·
        refine ⟨48459252810557276267620103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32306168540371517511746735 48459252810557276267620103)
        ·
          refine ⟨72688879215835914401430155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48459252810557276267620103 72688879215835914401430155)
          ·
            refine ⟨109033318823753871602145233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72688879215835914401430155 109033318823753871602145233)
            ·
              refine ⟨81774989117815403701608925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109033318823753871602145233 81774989117815403701608925)
              ·
                refine ⟨30665620919180776388103347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81774989117815403701608925 30665620919180776388103347)
                ·
                  refine ⟨45998431378771164582155021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30665620919180776388103347 45998431378771164582155021)
                  ·
                    refine ⟨17249411767039186718308133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45998431378771164582155021 17249411767039186718308133)
                    ·
                      refine ⟨3234264706319847509682775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17249411767039186718308133 3234264706319847509682775)
                      ·
                        rfl

theorem cell23_6298708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6298708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298708 prefixEnd_6298708 := by exact prefixLift 6298708
  have htrace : WordTrace (prefixWord ++ tailWord_6298708) baseStart_6298708 baseEnd_6298708 := by
    simpa [prefixWord, tailWord_6298708, baseEnd_6298708] using wordTrace_append hprefix tailTrace_6298708
  have hstable : (prefixWord ++ tailWord_6298708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298708).length < 2 ^ (prefixWord ++ tailWord_6298708).sum := by decide
  have hdescent : baseEnd_6298708 < baseStart_6298708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298725 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_6298725 : Nat := 118140960795 + 6298725 * 2 ^ 59
def prefixEnd_6298725 : Nat := 4983230072969 + 3 ^ 40 * 6298725 * 2
def baseEnd_6298725 : Nat := 3234273435490973943170197

theorem tailTrace_6298725 : CollatzResearch.WordTrace tailWord_6298725 prefixEnd_6298725 3234273435490973943170197 := by
  unfold tailWord_6298725
  simp only [CollatzResearch.WordTrace]
  refine ⟨229733374105802536431345629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153155582737201690954230419 229733374105802536431345629)
  ·
    refine ⟨86150015289675951161754611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229733374105802536431345629 86150015289675951161754611)
    ·
      refine ⟨129225022934513926742631917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86150015289675951161754611 129225022934513926742631917)
      ·
        refine ⟨48459383600442722528486969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129225022934513926742631917 48459383600442722528486969)
        ·
          refine ⟨36344537700332041896365227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48459383600442722528486969 36344537700332041896365227)
          ·
            refine ⟨54516806550498062844547841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36344537700332041896365227 54516806550498062844547841)
            ·
              refine ⟨40887604912873547133410881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54516806550498062844547841 40887604912873547133410881)
              ·
                refine ⟨30665703684655160350058161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40887604912873547133410881 30665703684655160350058161)
                ·
                  refine ⟨22999277763491370262543621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30665703684655160350058161 22999277763491370262543621)
                  ·
                    refine ⟨4312364580654631924226929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22999277763491370262543621 4312364580654631924226929)
                    ·
                      refine ⟨3234273435490973943170197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312364580654631924226929 3234273435490973943170197)
                      ·
                        rfl

theorem cell23_6298725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_6298725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298725 prefixEnd_6298725 := by exact prefixLift 6298725
  have htrace : WordTrace (prefixWord ++ tailWord_6298725) baseStart_6298725 baseEnd_6298725 := by
    simpa [prefixWord, tailWord_6298725, baseEnd_6298725] using wordTrace_append hprefix tailTrace_6298725
  have hstable : (prefixWord ++ tailWord_6298725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298725).length < 2 ^ (prefixWord ++ tailWord_6298725).sum := by decide
  have hdescent : baseEnd_6298725 < baseStart_6298725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298742 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6298742 : Nat := 118140960795 + 6298742 * 2 ^ 59
def prefixEnd_6298742 : Nat := 4983230072969 + 3 ^ 40 * 6298742 * 2
def baseEnd_6298742 : Nat := 3234282164662100376657619

theorem tailTrace_6298742 : CollatzResearch.WordTrace tailWord_6298742 prefixEnd_6298742 3234282164662100376657619 := by
  unfold tailWord_6298742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14358374634171309270919655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153155996097827298889809653 14358374634171309270919655)
  ·
    refine ⟨21537561951256963906379483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14358374634171309270919655 21537561951256963906379483)
    ·
      refine ⟨32306342926885445859569225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537561951256963906379483 32306342926885445859569225)
      ·
        refine ⟨24229757195164084394676919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32306342926885445859569225 24229757195164084394676919)
        ·
          refine ⟨36344635792746126592015379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24229757195164084394676919 36344635792746126592015379)
          ·
            refine ⟨54516953689119189888023069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36344635792746126592015379 54516953689119189888023069)
            ·
              refine ⟨20443857633419696208008651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54516953689119189888023069 20443857633419696208008651)
              ·
                refine ⟨30665786450129544312012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20443857633419696208008651 30665786450129544312012977)
                ·
                  refine ⟨22999339837597158234009733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30665786450129544312012977 22999339837597158234009733)
                  ·
                    refine ⟨4312376219549467168876825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22999339837597158234009733 4312376219549467168876825)
                    ·
                      refine ⟨3234282164662100376657619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312376219549467168876825 3234282164662100376657619)
                      ·
                        rfl

theorem cell23_6298742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6298742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298742 prefixEnd_6298742 := by exact prefixLift 6298742
  have htrace : WordTrace (prefixWord ++ tailWord_6298742) baseStart_6298742 baseEnd_6298742 := by
    simpa [prefixWord, tailWord_6298742, baseEnd_6298742] using wordTrace_append hprefix tailTrace_6298742
  have hstable : (prefixWord ++ tailWord_6298742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298742).length < 2 ^ (prefixWord ++ tailWord_6298742).sum := by decide
  have hdescent : baseEnd_6298742 < baseStart_6298742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
